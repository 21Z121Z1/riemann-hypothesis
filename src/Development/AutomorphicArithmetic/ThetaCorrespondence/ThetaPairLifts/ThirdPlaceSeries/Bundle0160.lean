import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0799
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0133
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0798
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0155
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0801
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0149
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0607
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0083
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0055
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0095
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0795
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0156
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0802
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0796
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0138
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0084
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0104

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreAlt
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
noncomputable section
namespace GlobalTheory.FrameInt
theorem main_alt_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (k : Fin (w.st Z).toD7.R.m) s,
    (∀ κ ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV,
      Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc (w.st Z).toD7 k) ((ad.PV k).ψ κ) ∈ Formalism.L2.DIV.St (t.r.z.R.βV k)) ∧
    ∀ PP, PP ∈ t.r.z.R.Pg ∨ PP ∈ t.r.z.R.Q s → ∃ (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin (w.st Z).toD7.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w = PP ∧ GlobalTheory.CenFrame.IsResidue s' φ ∧
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV (w.st Z).toD7 k) (ad.PV k) (t.r.z.R.βV k) s' φ b :=
  fun hL => GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun K B f T _ w Z Wt p0 t nch n xd c _ _ _ ad k s =>
    frame_of (D := (w.st Z).toD7) t.r.z.R.toLevCh t.r.z.pins.char.base.lev t.r.Y.hF k (ad.PV k) (ad.std k) s
end GlobalTheory.FrameInt
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreBisStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residue_ne_zero_ne_one_at_member : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ PP ∈ t.r.z.R.Pg, ∃ x : Formalism.L2.DIV.kP PP, x ≠ 0 ∧ x ≠ 1 := by
  first | exact @_root_.GlobalTheory.ResThree.main_alt_alt | exact _root_.GlobalTheory.ResThree.main_alt_alt | (intros; apply _root_.GlobalTheory.ResThree.main_alt_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsBuiltEPrmAIffStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberE_extensionWithAtProperty_of_evLgG : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP) (A : AtP), EvLgG A → MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ).s → MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL N A) S Γ).s := by
  first | exact @_root_.GlobalTheory.Mem.LiteralAutomorphy.memberE_extensionWithAtProperty_of_memberE | exact _root_.GlobalTheory.Mem.LiteralAutomorphy.memberE_extensionWithAtProperty_of_memberE | (intros; apply _root_.GlobalTheory.Mem.LiteralAutomorphy.memberE_extensionWithAtProperty_of_memberE <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LastStepIntegrableOnStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_step_vector_property_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ j (h : j + 2 * 0 + 2 = D.R.m) v, IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ΛX ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX ((_root_.GlobalTheory.Fam.pk_z W).datYt W.P.A3.A.μ0 (j + 1) (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi D.R.m) ((_root_.GlobalTheory.Fam.pk_z W).Q W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).xiR W.P.A3.A.μ0) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) v → ∀ (F : CXP (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) W.P.A3.A.μ0) Q x g, IntegrableOn (fun y => thetaKO (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h) g y (pureTensorO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D (j + 1)) D.sp.X' (cart ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (cart (_root_.GlobalTheory.Fam.pk_z W).MX) (onb ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1))) (onb (_root_.GlobalTheory.Fam.pk_z W).MX) v Q) * F.1 x y) ((_root_.GlobalTheory.Fam.pk_z W).fdX W.P.A3.A.μ0) ((_root_.GlobalTheory.Fam.pk_z W).νX W.P.A3.A.μ0) := by
  first | exact @_root_.GlobalTheory.BaseChain.lastStep_integrableOn_alt | exact _root_.GlobalTheory.BaseChain.lastStep_integrableOn_alt | (intros; apply _root_.GlobalTheory.BaseChain.lastStep_integrableOn_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MatchingCoset
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.MiTop
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
theorem mem_rJ_of_red_alt (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (z : GA D (D.sp.Y 0)) (hz : z ∈ GfC (D.sp.Y 0))
    (hS : Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from z) ∈ Formalism.L2.DIV.St (W.Q.Rl.βY 0))
    (hR : ∀ PP ∈ (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)).Pg,
      Formalism.L2.DIV.redFn (W.Q.Rl.βY 0) PP (Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from z)) = 1) :
    z ∈ _root_.GlobalTheory.MiTop.rJ_z W := by
  refine ⟨hz, ?_⟩
  refine GlobalTheory.LevSplit.mem_lev_of_red _ _ _ _ _ (GlobalTheory.LevSplit.finE_mem_UA _ _) hS ?_
  rintro PP (hP | hP)
  · exact hR PP hP
  · exact absurd hP (Finset.notMem_empty _)
theorem reduced_character_conj_eq_of_mem_level_group (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {k κ : GA D (D.sp.Y 0)} (hk : k ∈ _root_.GlobalTheory.MiTop.rJ_z W) (hκ : κ ∈ _root_.GlobalTheory.MiTop.rJ_z W) :
    _root_.GlobalTheory.MiTop.realCharacter W (k * κ * k⁻¹) = _root_.GlobalTheory.MiTop.realCharacter W κ := by
  have h1 : Formalism.IndefR.Lev.finE (Yc D 0) k ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)) := hk.2
  have h2 : Formalism.IndefR.Lev.finE (Yc D 0) κ ∈ Formalism.L2.DIV.lev D.sp.cm (Yc D 0).gram (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)) := hκ.2
  have e := levFn_conj D.sp.cm (Yc D 0).gram (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true)) h1 h2
  unfold _root_.GlobalTheory.MiTop.realCharacter Formalism.IndefR.Lev.levChi
  erw [map_mul, map_mul, map_inv, e]
theorem mem_rJ_iff_conj_mem (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {k κ : GA D (D.sp.Y 0)} (hk : k ∈ _root_.GlobalTheory.MiTop.rJ_z W) : κ ∈ _root_.GlobalTheory.MiTop.rJ_z W ↔ k * κ * k⁻¹ ∈ _root_.GlobalTheory.MiTop.rJ_z W := by
  have := (Subgroup.mul_mem_cancel_right (Formalism.IndefR.Lev.levG (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))) (y := k * κ) (Subgroup.inv_mem _ hk)).trans
    (Subgroup.mul_mem_cancel_left (Formalism.IndefR.Lev.levG (Yc D 0) (W.Q.Rl.βY 0) (W.Q.Rl.dat0 (W.Q.Rl.toRealDat.levR W.Q.F.lv2 true))) (y := κ) hk)
  exact this.symm
theorem matches_mul_of_mem_rJ (W : _root_.GlobalTheory.MiS.RealPackAlt ex) {z t k : GA D (D.sp.Y 0)} (hzf : z ∈ GfC (D.sp.Y 0))
    (hzc : z ∈ Subgroup.center (GA D (D.sp.Y 0))) (hk : k ∈ _root_.GlobalTheory.MiTop.rJ_z W) (ht : Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) t) :
    Matches W.S.X W.Q.instEq (_root_.GlobalTheory.MiTop.rJ_z W) (_root_.GlobalTheory.MiTop.realCharacter W) (z * t * k) := by
  have hkf : k ∈ GfC (D.sp.Y 0) := hk.1
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hzf ht.1) hkf, fun κ => ?_⟩
  have hz := Subgroup.mem_center_iff.mp hzc
  have hc : (z * t * k)⁻¹⁻¹ * κ * (z * t * k)⁻¹ = t⁻¹⁻¹ * (k * κ * k⁻¹) * t⁻¹ := by
    have e : (z * t * k)⁻¹⁻¹ * κ * (z * t * k)⁻¹ = z * (t⁻¹⁻¹ * (k * κ * k⁻¹) * t⁻¹) * z⁻¹ := by group
    rw [e, ← hz, mul_inv_cancel_right]
  obtain ⟨h1, h2⟩ := ht.2 (k * κ * k⁻¹)
  rw [hc]
  refine ⟨(_root_.GlobalTheory.MiTop.mem_rJ_iff_conj_mem W hk).trans h1, fun hκ => ?_⟩
  rw [h2 ((_root_.GlobalTheory.MiTop.mem_rJ_iff_conj_mem W hk).1 hκ), _root_.GlobalTheory.MiTop.reduced_character_conj_eq_of_mem_level_group W hk hκ]
theorem matching_coset_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → GlobalTheory.MiTop.Framed B → GlobalTheory.MiTop.Framed B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∃ a₁, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a₁ ∧ ∃ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.translationElement f B a₀ a₁ = _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k := by
  intro D L hT Gi Gl Kc Yd cX ex W hW hr u u' f f' B B' hP hP' hF hF' a₀ a a₀' a' hA hA'
  obtain ⟨z, hzf, hzc, c, hcf, hcc, k, hk, he⟩ :=
    _root_.GlobalTheory.T.matching_translates_bottom_alt W hW.bot hr u B (_root_.GlobalTheory.MiTop.translationElement f B a₀ a) hA.2.2.2.1 (_root_.GlobalTheory.MiTop.translationElement f' B' a₀' a') hA'.2.2.2.1 hA.2.2.2 hA'.2.2.2
  have hcc' := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hcc)
  have hX : _root_.GlobalTheory.MiTop.translationElement f B a₀ (a * c⁻¹) = ((iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u))⁻¹ * embA B.d B.o c⁻¹ *
      (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) * _root_.GlobalTheory.MiTop.translationElement f B a₀ a := by
    unfold _root_.GlobalTheory.MiTop.translationElement
    rw [show a₀ * (a * c⁻¹) = c⁻¹ * (a₀ * a) by rw [← hcc' (a₀ * a), mul_assoc], map_mul]
    have key : ∀ {G : Type} [Group G] (x e y b : G), x⁻¹ * (e * y) * b = x⁻¹ * e * x * (x⁻¹ * y * b) := by
      intros; group
    exact key (G := GA D (D.sp.Y 0)) _ _ _ _
  have e1 : _root_.GlobalTheory.MiTop.translationElement f B a₀ (a * c⁻¹) = z * _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k := by
    rw [hX, he, map_inv]
    simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]
  have hA₁ : _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ (a * c⁻¹) := by
    refine ⟨hA.1, Subgroup.mul_mem _ hA.2.1 (Subgroup.inv_mem _ hcf),
      Subgroup.mul_mem _ hA.2.2.1 (Subgroup.inv_mem _ hcc), ?_⟩
    rw [e1]
    exact _root_.GlobalTheory.MiTop.matches_mul_of_mem_rJ W hzf hzc hk hA'.2.2.2
  have hz : z ∈ _root_.GlobalTheory.MiTop.rJ_z W := _root_.GlobalTheory.MiTop.mem_rJ_of_red_alt W z hzf
    (by first
      | exact _root_.GlobalTheory.T.placed_bessel_pair_relation_alt W hW hr u u' f f' B B' hP hP' hF hF' a₀ (a * c⁻¹) a₀' a' hA₁ hA' z hzf hzc k hk e1
      | exact _root_.GlobalTheory.T.placed_bessel_pair_relation_alt W hW hr u u' f f' B B' hP hP' a₀ (a * c⁻¹) a₀' a' hA₁ hA' z hzf hzc k hk e1)
    (by first
      | exact _root_.GlobalTheory.T.placed_bessel_pair_identity_alt W hW hr u u' f f' B B' hP hP' hF hF' a₀ (a * c⁻¹) a₀' a' hA₁ hA' z hzf hzc k hk e1
      | exact _root_.GlobalTheory.T.placed_bessel_pair_identity_alt W hW hr u u' f f' B B' hP hP' a₀ (a * c⁻¹) a₀' a' hA₁ hA' z hzf hzc k hk e1)
  refine ⟨a * c⁻¹, hA₁, z * k, Subgroup.mul_mem _ hz hk, ?_⟩
  rw [e1, ← (Subgroup.mem_center_iff.mp hzc (_root_.GlobalTheory.MiTop.translationElement f' B' a₀' a')), mul_assoc]
end GlobalTheory.MiTop
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MtInputOfStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_frame_split_nontrivial_at_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (i : (w.st Z).toD7.nd.Loc) s (k : Fin (w.st Z).toD7.R.m), t.r.Y.tup s = (w.st Z).toD7.nd.mu i →
    Nontrivial ((w.st Z).toD7.what₂.Mt (t.r.Y.tup s) ((k : ℕ) + 1)) →
    ∀ (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin (w.st Z).toD7.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w ∈ t.r.z.R.Pg → GlobalTheory.CenFrame.IsResidue s' φ →
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV (w.st Z).toD7 k) (ad.PV k) (t.r.z.R.βV k) s' φ b →
        ∃ (f : Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.nV → ℂ) (J : Subgroup (Formalism.AUTREP.GAf (w.st Z).toD7.host.E (w.st Z).toD7.R.nV)) (χ : J →* ℂˣ)
          (ψ₀ : AddChar (s'.v.adicCompletion (NumberField.maximalRealSubfield (w.st Z).toD7.host.E)) ℂ)
          (ξ : (s'.v.adicCompletion (NumberField.maximalRealSubfield (w.st Z).toD7.host.E))ˣ →* ℂˣ),
          f ≠ 0 ∧ Formalism.L2.NG.IsPsi0 s' ψ₀ ∧ Formalism.L2.NG.LevelUni J χ s' (w.st Z).toD7.R.r ψ₀ ξ ∧
          (∀ κ (h : κ ∈ J) g, f (g * κ) = ((χ ⟨κ, h⟩ : ℂˣ) : ℂ) * f g) ∧
          (∀ κ ∈ ReciprocityTheory.Aut.Umax (w.st Z).toD7.host.E (w.st Z).toD7.R.nV, ReciprocityTheory.Aut.TrivOutside {s'.v} κ → ∀ y : GL (Fin (w.st Z).toD7.R.nV) (GlobalTheory.CenFrame.Os s'),
        GlobalTheory.CenFrame.IsCompOf s' κ y →
      ((∀ i j : Fin (w.st Z).toD7.R.nV, ((w.st Z).toD7.R.r ≤ i.val → j.val < (w.st Z).toD7.R.r → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 0) ∧
        (i.val < (w.st Z).toD7.R.r → j.val < i.val → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 0) ∧
        (i.val < (w.st Z).toD7.R.r → i = j → (b * Matrix.GeneralLinearGroup.map φ y * b⁻¹).val i j = 1)) →
        ∃ c : ℂ, ∀ g, f (g * κ) = c * f g) ∧
      (Matrix.GeneralLinearGroup.map φ y = 1 → ∀ g, f (g * κ) = f g)) := by
  first | exact @_root_.GlobalTheory.FrameTypes.main_alt_alt | exact _root_.GlobalTheory.FrameTypes.main_alt_alt | (intros; apply _root_.GlobalTheory.FrameTypes.main_alt_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NdSpecExists
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
noncomputable section
namespace GlobalTheory.HeckeLocN
set_option synthInstance.maxHeartbeats 400000
section Psi
variable {D : D7} {C : NChoice D} {X : CoefIn D.what₂} {ψ0 : D.what₂.places.Pl → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)}
  (hψ0 : ∀ w g, C.embW w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) =
    algebraMap (C.Oe w) (FractionRing (C.Oe w)) (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w)
      ((C.psi' w (D.ntw.art (C.twI w) (C.Q w) g) : (D.ntw.Ok (C.twI w) (C.k' w))ˣ) : D.ntw.Ok (C.twI w) (C.k' w))))
  (hP : PsiInt X ψ0) (j : ℕ) (w : D.what₂.places.Pl)
end Psi
set_option maxHeartbeats 2000000 in
theorem ndSpec_exists_alt : GlobalTheory.Published.GlobalArtinReciprocity → HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → ∀ big : D.what₂.places.Pl → Finset ℂ, ∃ (X : LocNd (lay0 D)) (T : LocTw X), Nonempty (NdSpec A.pl M C big X T) := by
  intro hArt hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI _ _ hpd hCheb hOS hVal big
  obtain ⟨hO, hc⟩ := GlobalTheory.T.twistConductors_over_real_places_and_conj_stable D cf C tp hCS.off
  have hG := GlobalTheory.T.heckeGeneratorPlacesOutsideLevel_of_stable D cf M C tp hMI hO
  have hX := GlobalTheory.T.exists_conjugate_splitPlace_and_uniformizer D
  have hR := GlobalTheory.T.exists_coefficientLinear_lift_doubleCosetOperators D M C tp.tup hStd hG hMI
  have hCm := GlobalTheory.T.liftedHeckeOperators_at_generators_commute D M C hR hStd hG hX
  choose F1 hF1 using GlobalTheory.T.exists_padicFiniteExt_containing_all_hecke_eigenvalues D M C hR (plEmb A.pl) hCm
  choose F2 hF2 hF2' using GlobalTheory.T.exists_padicFiniteExt_containing_coeffField_and_numbers D A.pl big
  choose F3 hF3 using GlobalTheory.T.localBridges_at_placesOverResidueChar_of_large_coeff D
  choose F4 hF4 using GlobalTheory.T.exists_twist_ring_map_large_coefficient_rings D C Bs.twF low (plEmb A.pl) Bs.tw hCS.choice
  obtain ⟨X, hXE, h1, h2, h3, h4⟩ : ∃ X : CoefIn D.what₂, X.E = plEmb A.pl ∧ (∀ j w, (F1 j w).1 ≤ (X.Kx j w).1) ∧
      (∀ j w, (F2 w).1 ≤ (X.Kx j w).1) ∧ (∀ j w, (F3 w).1 ≤ (X.Kx j w).1) ∧ ∀ j w, (F4 w).1 ≤ (X.Kx j w).1 :=
    ⟨coefIn A.pl (fun j w => feSup (feSup (F1 j w) (F2 w)) (feSup (F3 w) (F4 w)))
      (fun j w x => (le_sup_of_le_left le_sup_right : (F2 w).1 ≤ ((F1 j w).1 ⊔ (F2 w).1) ⊔ ((F3 w).1 ⊔ (F4 w).1)) (hF2 w x)), rfl,
      fun _ _ => le_sup_of_le_left le_sup_left, fun _ _ => le_sup_of_le_left le_sup_right,
      fun _ _ => le_sup_of_le_right le_sup_left, fun _ _ => le_sup_of_le_right le_sup_right⟩
  have hS : SplitK (mt0 M) C.Q hR X := fun j w => hF1 j w X hXE (h1 j w)
  choose twC hTwA hTwR hTwE using fun j w => hF4 w X j hXE (h4 j w)
  obtain ⟨ψ0, -, hψ0, -⟩ := hCS.nct.psi_eq
  have hP := GlobalTheory.T.twistCharacterValues_integral_units_at_place D C X ψ0 hψ0
  have hs := GlobalTheory.T.heckeStandardFacts_on_localisation_base D M C hR X hS hStd hG hX hCm
  have hd := GlobalTheory.T.finiteDimensional_localisation_space_all (base M C hR X hS)
  have hML := LatticeFinitenessFree.mtLoc_holds (partCompl_of hs hd)
  have hAct := GlobalTheory.T.heckeRing_acts_faithfully_on_localisedLattice _ hs hd hML (GlobalTheory.T.heckeOperator_integral_on_lattice_at_twisted_places D M C hR X hS tp.tup hMI hX)
    (GlobalTheory.T.heckeOperators_on_localisation_space_semisimple D M C hR X hS hStd GlobalTheory.T.splitPlace_doubleCosetOperator_semisimple_typeSpace hG hX)
  have hAHK := GlobalTheory.T.heckeRing_acts_on_lattice_as_operators _ hs hd hML hAct
  have hI := osInt D (base M C hR X hS)
  have hGal := fun w (hw : TwistedAt D w) => GlobalTheory.T.twistCharacter_ramified_at_conductor_trivial_above_l D cf C tp w hArt hCheb hCS.psi hw (hVal w hw) (hCS.adm w hw)
  have htw : ∀ w v, v ∈ C.Q w → TwistedAt D w := fun w v hv => by
    by_contra hw
    rw [hCS.off w hw] at hv
    exact absurd hv (Finset.notMem_empty v)
  have hQl : ∀ w v, v ∈ C.Q w → v ∉ placesOver D.host.E (D.what₂.places.resChar w) := fun w v hv =>
    C.twI_l w ▸ ((hCS.adm w (htw w v hv)).1 v hv).2
  have hQS : ∀ w v, v ∈ C.Q w → v ∉ exceptionalPlaces D.host (D.what₂.places.resChar w) := fun w v hv h => by
    have ha := (hCS.adm w (htw w v hv)).2.1 v hv
    rcases h.1 with h | h | h
    · exact ha.2 0 h
    · exact ha.2 1 h
    · refine ha.1 (Finset.mem_coe.1 ?_)
      rw [D.ntw.pD_eq, C.twI_l]
      exact h
  have hSs : ∀ l v, v ∈ exceptionalPlaces D.host l → IsSplitPl D.host v := fun l v h => by
    rcases h.1 with h | h | h
    · exact GlobalTheory.T.typePrime_places_isSplitPlace D 0 v h
    · exact GlobalTheory.T.typePrime_places_isSplitPlace D 1 v h
    · split_ifs at h
      · exact hpd v (Or.inr h)
      · exact hpd v (Or.inl h)
  have hRP := fun j w (hw : TwistedAt D w) => psN_ram hψ0 hP j w (hGal w hw).1
  refine ⟨_, _, nonempty_spec (base M C hR X hS) C hs hd hML (LatticeFinitenessFree.mtSub_free _) (LatticeFinitenessFree.mtSub_finite _) (GlobalTheory.T.localisation_heckeRing_isLocalRing _ hs hd) hAct
    (GlobalTheory.T.heckeEigenspace_ne_bot_every_localisation_point _ hs hd hML hAct hAHK) (fun i => twC (jOf _ i) (wOf _ i)) (fun i => psN X ψ0 hP (jOf _ i) (wOf _ i))
    (GlobalTheory.T.localisation_galoisCharacter_continuous D M C hR X hS twC ψ0 hP hTwA (psN_open hψ0 hP))
    (fun i v hv => hv.elim (fun h => hSs _ v ((Set.Finite.mem_toFinset _).1 h))
      (fun h => ((hCS.adm _ (htw _ v h)).1 v h).1))
    (fun i => Finset.disjoint_left.2 fun v h h' => hQS _ v h' ((Set.Finite.mem_toFinset _).1 h)) hQl ?_ hI
    (GlobalTheory.T.latticeBaseChange_free_over_localisation_coeffRing D _ hI hOS) (fun a => hTwE _ _ a.2.2.2.2.2) (fun a => psN_ord hψ0 hP _ _) (fun a => psN_open hψ0 hP _ _)
    (fun a => psN_anti hψ0 hP _ _) (fun a => hRP _ _ a.2.2.2.2.2)
    (fun a v hv B hB σ hσ => (psN_eq_one hψ0 hP _ _ σ).2 ((hGal _ a.2.2.2.2.2).2 v hv B hB σ hσ))
    A.pl M big (fun j w h1 h2 v k s ϖ hg hcj hu x => hLC_spec (mt0 M) C.Q hR j w v k h1 h2 hg s ϖ hcj hu x) hO hc
    (fun _ => rfl) (iqC X) (fun j w z => (iqC_alg X j w _).trans rfl) ?_ ?_ hAHK (plGwDisj D) ?_ (fun a => hTwA _ _)
    (fun a => hTwR _ _) (fun j w => hF3 w X j (h3 j w))⟩
  · intro i v hv
    have hw : TwistedAt D (wOf _ i) := i.2.2.2.2.2
    obtain ⟨σ, hσ, hne⟩ := (hRP (jOf _ i) _ hw v _ (D.nd.plOm.2 v)).2 hv
    have ha := hCS.adm _ hw
    have h1 := D.ntw.twistCharacterFamily_unramified (C.twI (wOf _ i)) (jOf _ i) (C.sd (wOf _ i)) v (ha.1 v hv).2 (ha.2.1 v hv).2 (ha.2.1 v hv).1 _
      (D.nd.plOm.2 v) σ hσ
    refine ⟨σ, hσ, fun e => hne ?_⟩
    have e' : Units.map (twC (jOf _ i) (wOf _ i)).toMonoidHom (D.ntw.chi1 (C.twI (wOf _ i)) (jOf _ i) (C.sd (wOf _ i)) σ) *
        psN X ψ0 hP (jOf _ i) (wOf _ i) σ = 1 := e
    rwa [h1, map_one, one_mul] at e'
  · intro j w x
    change A.pl.ι w (iqC X j w (ecC X j w x)) = _
    rw [iqC_ec, hXE]
    exact (A.pl.ι w).apply_symm_apply _
  · intro j w z hz
    obtain ⟨x, hx⟩ := iqC_surj X j w _ (h2 j w (hF2' w z hz))
    exact ⟨x, (congrArg (A.pl.ι w) hx).trans ((A.pl.ι w).apply_symm_apply z)⟩
  · intro a g y hy
    obtain rfl := (C.embW _).injective (hy.trans (hψ0 _ g).symm)
    exact (psN_spec hP _ _ g).symm
end GlobalTheory.HeckeLocN
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OpinAtMemStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_duty_pin_at_each_member : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => _root_.GlobalTheory.CoefDuty.OPinAlt c.a := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.oPin_at_mem | exact _root_.GlobalTheory.HeightCounting.Up.oPin_at_mem | (intros; apply _root_.GlobalTheory.HeightCounting.Up.oPin_at_mem <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParInBuilt
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.RowTriple.Lay.EigCopy
set_option maxHeartbeats 4000000 in
theorem parIn_built_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D' cf' C' tp') (rep' : D'.what₂.FT → NG.FinTyp D'.host.E D'.R.r)
    (hrep : HEq nt.rep rep') :
    ∃ Rw : RowSide D', HEq Rw.locR nt.A.row.locR ∧ Nonempty (_root_.GlobalTheory.HeightCounting.Up.ParityConditions hL D' cf' rep' Rw) := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp pack
  obtain ⟨hcf, -⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h2)
  subst hcf
  have hr : rep = rep' := eq_of_heq hrep
  subst hr
  let T : GlobalTheory.RowTie.WDTie (withLoc L).nd (withLoc L).naut := { A.wdT with }
  let Rw : RowSide (withLoc L) := { A.row with }
  exact ⟨Rw, HEq.rfl, ⟨{ T := T, lab := A.lab, chr := { A.chr with }, cg := { cg with }, A := { A.au with }, au := au, row := row }⟩⟩
end GlobalTheory.RowTriple.Lay.EigCopy
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PenLocFacStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_geometry_finite_index_alt_alt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (n : Fin a.n) (j : ℕ) (hj : j + 1 ≤ B.R.m), j + 2 = B.R.m → ∃ c : ℂ, c ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) (γ : J.Ch (j + 1)), ∃ Ξ : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E → ℂ, GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.pl n).1 ((a.G n).cg j) Ξ ∧ ∀ (P : GlobalTheory.QTw.BadPr I (W.P.I.tup t)), P.1 = (a.pl n).1 → ∀ z, B.embLL (GlobalTheory.QTw.locXi J.A j (J.ι j α) (J.ι (j + 1) γ) P (GlobalTheory.QTw.homOf I l Z j hj z)) = c * Ξ z := by
  first | exact @_root_.GlobalTheory.Fam.PenLoc.pen_locFac_alt | exact _root_.GlobalTheory.Fam.PenLoc.pen_locFac_alt | (intros; apply _root_.GlobalTheory.Fam.PenLoc.pen_locFac_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacedOfTrueStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placed_p_of_true_geometry : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → _root_.GlobalTheory.MiTop.PlacedConditions (a.fam row col) a.d.B := by
  first | exact @_root_.GlobalTheory.FamPlaced.placedP_of_allTrue | exact _root_.GlobalTheory.FamPlaced.placedP_of_allTrue | (intros; apply _root_.GlobalTheory.FamPlaced.placedP_of_allTrue <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesSt
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.TupLe
variable {D : D7}
open Classical in
theorem placesSt_alt : _root_.GlobalTheory.BigOn.Exp.TupLe.PlacesCondition := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j hr hm w hw hok ρ hρ hpin _ _
  have hPA := placesAt (j := j) hw hρ hpin
  have hL := _root_.GlobalTheory.BigOn.links2_of_rows_alt _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hXs : SplitSet (p.R.Q (p.R.mu (D.plEq w))) := by
    obtain ⟨-, e, he, -⟩ := hC.thP.vP j (p.R.mu (D.plEq w))
    exact SplitSet.mono ⟨e, he⟩ Finset.subset_union_right
  have hl : ∀ P ∈ p.R.Q (p.R.mu (D.plEq w)), ((D.ntw.l (ex.nch.twI w) : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro P hP
    rcases (hPA.2 P).1 (Or.inl hP) with hD | hQ
    · have h1 : P ∈ (↑(D.ntw.pD (ex.nch.twI w)) : Set (Pl D.host.E)) := hD
      rw [D.ntw.pD_eq] at h1
      have hlp := (D.ntw.lPrime (ex.nch.twI w)).out
      refine not_mem_of_coprime h1 ?_
      split_ifs with h
      · exact (Nat.coprime_primes hlp D.host.pde'_prime).2 (by rw [h]; exact D.host.pde_ne)
      · exact (Nat.coprime_primes hlp D.host.pde_prime).2 h
    · exact fun hlP => Finset.disjoint_left.1 hok.2.1 hQ (D.ntw.twistExcludedPlaces_contains_residueChar _ hlP)
  refine ⟨hXs, hl, ?_⟩
  obtain ⟨-, hadm, -⟩ := GlobalTheory.TwistGood.tw_good D _ D.ntw ρ hρ _ j (ex.nch.sd w) _ _ _ hok
  obtain ⟨R, -, hR, hRs⟩ := hadm.1.split
  have hYs := hRs.mono hR
  have hXC : ∀ P, P ∈ p.R.Q (p.R.mu (D.plEq w)) ∪ (p.R.Q (p.R.mu (D.plEq w))).image Formalism.L2.DIV.conjPl ↔
      (P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w) := fun P => by
    rw [← hPA.2 P, Finset.mem_union, Finset.mem_image]
    refine or_congr Iff.rfl (exists_congr fun P' => and_congr Iff.rfl ?_)
    rw [lev_isConjPl_iff, eq_comm]
  have hne : ∀ P, P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w → Formalism.L2.DIV.conjPl P ≠ P := fun P hP e => by
    rcases Finset.mem_union.1 ((hXC P).2 hP) with h | h
    · exact Finset.disjoint_left.1 (disjoint_conj hXs) h (Finset.mem_image.2 ⟨P, h, e⟩)
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 h
      rw [Formalism.L2.DIV.conjPl_conjPl] at e
      exact Finset.disjoint_left.1 (disjoint_conj hXs) hP' (Finset.mem_image.2 ⟨P', hP', e.symm⟩)
  have hcl : ∀ P, P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w →
      Formalism.L2.DIV.conjPl P ∈ D.ntw.pD (ex.nch.twI w) ∨ Formalism.L2.DIV.conjPl P ∈ ex.nch.Q w := fun P hP => by
    rw [← hXC] at hP ⊢
    rcases Finset.mem_union.1 hP with h | h
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
    · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.1 h
      rw [Formalism.L2.DIV.conjPl_conjPl]
      exact Finset.mem_union_left _ hP'
  have hY : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.Q ∪
      (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).Q =
      half (ρ.ch (ex.nch.twI w)) (D.ntw.pD (ex.nch.twI w)) ∪ half (ρ.ch (ex.nch.twI w)) (ex.nch.Q w) := by
    rw [hρ.delta]
    rfl
  rw [hY] at hYs ⊢
  exact idem_add_cA_eq hXs hYs fun P =>
    (hXC P).trans (mem_half_closure ((hρ.ch _).pair) hcl hne P).symm
end GlobalTheory.BigOn.Exp.TupLe
end
end
end

