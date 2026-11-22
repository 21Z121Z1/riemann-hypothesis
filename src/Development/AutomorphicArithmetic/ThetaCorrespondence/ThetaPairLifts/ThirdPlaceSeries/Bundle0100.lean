import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0538
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0061
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0064
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0070
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0091
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0903
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0039
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0089
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0001
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0099
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0074
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2123
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0084
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0093
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2113
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0533
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0560
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0060
import Formalism.LocalToGlobal.Bundle0003
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0040
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0065
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0080
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0066
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0032
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RelaxPhiMemKO
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.LevProd
theorem relax_phi_mem_KO_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t' (J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t'), J'.Reads → ∀ g ∈ _root_.GlobalTheory.LevProd.relaxedLevelSubgroup J j hj α, ∀ i, _root_.GlobalTheory.LevProd.localHomProduct J' j hj g i ∈ KO (J'.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α t' J' hJ' g hg i
  obtain ⟨⟨hsup, hgf⟩, hphi⟩ := Subgroup.mem_inf.1 hg |>.imp_left Subgroup.mem_inf.1
  by_cases hv : _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J (J'.G i).q.v
  · obtain ⟨i₀, hi₀⟩ := hv
    exact _root_.GlobalTheory.T.true_geometry_lattice_closed_alt W hW u a ha hTr j hj t J hJ t' J' hJ' i₀ i hi₀ g hgf
      ((Subgroup.mem_pi _).1 (Subgroup.mem_comap.1 hphi) i₀ (Set.mem_univ _))
  · have hle : J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J) ≤
        (KO (J'.G i).k _).comap ((Pi.evalMonoidHom _ i).comp (_root_.GlobalTheory.LevProd.localHomProduct J' j hj)) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact _root_.GlobalTheory.T.true_geometry_lattice_final_alt W hW u a ha hTr j hj t J hJ α t' J' hJ' i hv x hx
      · rw [Subgroup.mem_comap, MonoidHom.comp_apply, Pi.evalMonoidHom_apply]
        change GlobalTheory.LevIdx.locHom (J'.G i).q _ _ x ∈ KO (J'.G i).k _
        rw [locHom_eq_one_of_grpAt' _ _ _ hv hx]
        exact one_mem _
    exact hle hsup
end GlobalTheory.LevProd
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RestPtOf
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
noncomputable section
namespace GlobalTheory.NLinkTameShape
theorem restPt_of_alt (hP : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (X : KillingConditions.HubData D) (C₂ : ℝ) (hS : _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂) (i : D.nd.Loc)
    (hi : D.nd.l i ∉ TwistedPlaces.gset D) (π : D.nd.X i) (hπ : π ∈ D.nd.Zgood i) : RestPt i (X.r i) (X.ρ i) π := by
  have hb : ((0 : ℕ) : ℝ) ≤ L.sc.b := by
    simp only [Nat.cast_zero]; unfold Scale.b; exact (Real.exp_pos _).le
  have hL : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have fa := hS.facts
  exact (_root_.GlobalTheory.T.split_bound_of_params_alt hP.font hP.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 0 hS.canon P hL le_rfl hb
    (fa.admJ L hS.par) hS.par67 fa.toCore.admA fa.Conclusion1.1 fa.Conclusion1.2.2 fa.Conclusion2.1 fa.Conclusion2.2.2 fa.rhoBar fa.large.2.1
    fa.large.2.2 fa.nct fa.trip fa.same fa.block fa.muUnr fa.depthG).2.2.2.2.2.2.2.1 i hi π hπ
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.admG5 i (X.r i) (X.ρ i) π := by
  intro hP D L P nch HW F Cm X C₂ hS i hi π hπ _ S hG
  have R := _root_.GlobalTheory.NLinkTameShape.restPt_of_alt hP D L P nch HW F X C₂ hS i hi π hπ
  have hHG : HG D.nd D.naut i := ⟨π, (D.Zgood_tie i π).1 hπ⟩
  have h32 := hS.facts.Conclusion2.1 i hHG (X.r i) R.good
  have hx := (GlobalTheory.TameDesign.main D i).2
  have hrb := isRhoBar_of_isRhoOf D i π (X.ρ i π) R.rho
  intro v hv
  have hl := D.nd.SQ_l i v hv
  obtain ⟨ha, hb, hc⟩ := h32 v hv hl
  refine ⟨(hx v hv).1, fun hq x => ?_, fun hk => ?_, fun hvS => ⟨?_, fun a => ?_⟩⟩
  · obtain ⟨hprod, Pm, hPm⟩ := ha hq x
    refine ⟨fun γ hγ => by simpa [rO, chi1] using hprod γ hγ, ?_⟩
    let ψ : (Fin D.R.nV → KK D.nd i) ≃ₗ[KK D.nd i] (Fin D.R.nV → KK D.nd i) :=
      LinearEquiv.ofLinear (Matrix.toLin' ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)))
        (Matrix.toLin' ((Pm : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)))
        (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one])
        (by rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin'_one])
    refine ⟨ψ.trans (Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL D.R.r D.R.t D.R.nV rfl), fun γ hγ u => ?_⟩
    have hM := hPm γ hγ
    have h1 : ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) *
        mapM (toK D.nd i) (rO D.nd i (X.r i) x) γ =
        Matrix.diagonal (fun k : Fin D.R.nV => if (k : ℕ) < D.R.r then 1 else
          algebraMap (D.nd.O i) (KK D.nd i) (chi1 D.nd i γ)) *
          ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) := by
      rw [← hM]
      have e : Pm⁻¹ * mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (X.r i x) γ =
          (Pm⁻¹ * mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (X.r i x) γ * Pm) * Pm⁻¹ := by group
      have e2 := congrArg (fun g : GL (Fin D.R.nV) (Kf D.nd i) => (g : Matrix (Fin D.R.nV) (Fin D.R.nV) (Kf D.nd i))) e
      simp only [Units.val_mul] at e2
      exact e2
    show Formalism.MainNotions.N.K.SplitLatticeDiagonal.splitL D.R.r D.R.t D.R.nV rfl
        (((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)).mulVec
          ((mapM (toK D.nd i) (rO D.nd i (X.r i) x) γ).mulVec u)) = _
    rw [Matrix.mulVec_mulVec, h1, ← Matrix.mulVec_mulVec]
    exact splitL_diagonal D.R.r D.R.t D.R.nV rfl _ _
  · obtain ⟨k, hk⟩ := hk
    have hvS : v ∈ D.nd.S i := by
      refine (D.nd.S_def i v).2 ⟨?_, hl⟩
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
    obtain ⟨Pp, hU, hPp⟩ := hb ⟨k, hk⟩ hvS
    exact ⟨Pp, fun x γ hγ => hPp x γ hγ, hU⟩
  · exact (hc hvS).1 (X.ρ i) π S (Formalism.MainNotions.SumRepresentations.At.inertia_props_of_idempotent_choice D.nd hG)
  · have H := (hc hvS).2 _ hrb a
    obtain ⟨H0z, H1z, H2z⟩ := H
    rw [rhoBarTw_eq]
    letI : TopologicalSpace (IsLocalRing.ResidueField (D.nd.O i)) := ⊥
    haveI : DiscreteTopology (IsLocalRing.ResidueField (D.nd.O i)) := ⟨rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · have e : H0 ((twistRep (glRep (redRep D.nd i (X.ρ i π))) (Formalism.MainNotions.SumRepresentations.At.chiEpsBar D.nd i a)).comp (decS D.nd v)) = ⊥ := H0z
      rw [e]
      infer_instance
    · convert H1z using 2
    · convert H2z using 2
end GlobalTheory.NLinkTameShape
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SideWExportSmall
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.FinalJoin2 GlobalTheory.AtMember GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.Plug GlobalTheory.PlugPt
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory
theorem sideW_export_small_alt : GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (𝒮 : Slots) (ν : _root_.GlobalTheory.PlugPt.ExtensionReading hL 𝒮) (K : Ctx) (p : WPt 𝒮 K), Nonempty (GlobalTheory.SeriesTie.ExportTie (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).YS (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).v₀) ∧ LevelIs (p.w.D p.Z).nexp ((_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).R.eG.trans (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cG) (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).P0 (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).ψ0⁻¹ ∧ AllData (p.w.D p.Z).nexp p.O.ex.xd.xd0 ∧ SmallHas (p.w.D p.Z) (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cf := by
  intro hR hL 𝒮 ν K p
  have hE : (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).Export p.O.ex.xd := (ν.rd _ _ _ _ _ _ _ _ _ _ _ _ p.x.nx).2.1.down
  have hcf : (_root_.GlobalTheory.PlugPt.sideOfWeightedPoint ν p).cf = Fr.at (p.w.st p.Z) p.f := (GlobalTheory.Plug.wPt_frame 𝒮 K p).2.1
  refine ⟨hE.1, hE.2.1, hE.2.2, ?_⟩
  rw [hcf]
  exact GlobalTheory.T.small_frame_at_column hR p.B p.f p.T p.w p.Z
end GlobalTheory
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizeAtStatement
section
set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_at' : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt := by
  first | exact @_root_.GlobalTheory.BigTop.Fun.SizeProof.sizeAt_alt | exact _root_.GlobalTheory.BigTop.Fun.SizeProof.sizeAt_alt | (intros; apply _root_.GlobalTheory.BigTop.Fun.SizeProof.sizeAt_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallStAltBis
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain
open NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links (PolF labLL)
open Formalism.L2.Host (embLL0)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SmallSpan
variable {D : D7} {m n : ℕ}
theorem smallSt_alt : _root_.GlobalTheory.BigOn.Exp.TupLe.SmallnessCondition := by
  intro D _ _ _ _ _ _ _ _ _ p j _ _ B hB _ O O' _ hO' h P hP
  exact harmLat_le_span D.LL0.val.toRingHom D.what₂.embLL (labLL0 D) O O' hO'.int B.w B.F.BS hB.wt
    (GlobalTheory.CoefLatConj.pq_le hB) (isLattice_latAt hB.frame _) hP
end GlobalTheory.SmallSpan
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallStStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_estimate : _root_.GlobalTheory.ExpTie.SmallnessCondition := by
  first | exact @_root_.GlobalTheory.ExpTie.smallSt_alt | exact _root_.GlobalTheory.ExpTie.smallSt_alt | (intros; apply _root_.GlobalTheory.ExpTie.smallSt_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TOfFixERStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placed_bessel_translate_vector_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (hr : 1 ≤ D.R.rS) u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → ∀ a₀ a, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → ∀ c : AE D, Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (_root_.GlobalTheory.MiTop.translationElement f B a₀ a)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) = Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) := by
  first | exact @_root_.GlobalTheory.MiTop.tOf_fix_eR_alt | exact _root_.GlobalTheory.MiTop.tOf_fix_eR_alt | (intros; apply _root_.GlobalTheory.MiTop.tOf_fix_eR_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TOfFixFirstStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_place_frame_exists_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (∃ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg, PP.under (𝓞 D.host.F) = v) → ∃ (e : Fin (D.sp.Y 0).rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E) (α : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ), ∀ u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedAlt f B → ∀ a₀ a, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → ∀ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, Matrix.mulVec ((GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig (D.sp.Y 0).gram (GlobalTheory.AdelicU.proj D.sp.cm.sig (D.sp.Y 0).gram v (_root_.GlobalTheory.MiTop.translationElement f B a₀ a)))⁻¹).val (c • e) ∈ GlobalTheory.AdelicU.latLoc D.host.F ((_root_.GlobalTheory.Fam.pk_z W).ΛY 0) v ↔ ((α⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E) * c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := by
  first | exact @_root_.GlobalTheory.LineAtG.line_atG_alt | exact _root_.GlobalTheory.LineAtG.line_atG_alt | (intros; apply _root_.GlobalTheory.LineAtG.line_atG_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameSt
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
namespace GlobalTheory.TameStab
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Groups
variable {G Γ : Type} [Group G] [Group Γ]
end Groups
theorem tameSt_alt : _root_.GlobalTheory.ExpTie.InRangeAlt fun _ _ _ _ p j P _ w => SmallAt p j P w → TameAt p j w := by
  unfold _root_.GlobalTheory.ExpTie.InRangeAlt _root_.GlobalTheory.BigOn.AtPtsAlt Formalism.MainNotions.Closed _root_.GlobalTheory.BigTop.EventuallyAtPoints
  refine ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ⟨0, fun x hx _ i p _ _ => ?_⟩⟩⟩
  intro j P W hD _ w _ _ hS
  exact tameAt_of_smallAt p j P w hD.Nr hS
end GlobalTheory.TameStab
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaEV0EqICPq
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Indef Formalism.IndefR.Cx GlobalTheory.BigTop GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BigTop.Fun
open Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Cx.CxData
open scoped InnerProductSpace Matrix
set_option maxHeartbeats 1000000 in
theorem theta_eV0_eq_iC_Pq_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' → ∀ (t : Tup p) (y : Fin ((Df p).nV t) → D.what₂.LL), (p.R.toCx3 p.F).Θ t ((p.R.toCx3 p.F).jR t (eV0 p t y)) = (p.R.toCx3 p.F).iC p.F.cr false t (cpt p.P.A3.fam3.base3.v0.embedding (((Df p).Pq t).mulVec y)) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hp t y
  have hCx := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hp.ok hp.sep p.charW hp.prim
  rw [iC_cpt_eq_theta_toR, TieModel.toR_eq]
  let y' : Fin ((p.P.A3.A.fam.R t).nV (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0)) → D.what₂.LL := y
  have hu := sub_zE_Pq_mem_U (p.P.A3.A.fam.R t) (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0) ((p.R.toCx3 p.F).zs.Z t)
    ((hCx.wf false).Pq_surj t) y'
  have h := theta_jR_eq_zero_of_perp _ p.F.cv hCx.jIsoR hCx.ratZ t (eV0 p t (y' - ((p.P.A3.A.fam.R t).zE (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0)
      ((p.R.toCx3 p.F).zs.Z t)).mulVec (((Df p).Pq t).mulVec y))) (fun w hw =>
    csum_goodPart_perp_eq_zero (p.P.A3.A.fam.R t) 1 (hp.ok.ok2.what₂ t) _ hp.ok.ok2.conj _ hp.ok.ok2.irr _
      (fun g => Submodule.map_le_iff_le_comap.mp (hCx.stable.1 t (Sum.inr g))) _ hu w hw)
  erw [(eV0 p t).map_sub] at h
  have h2 := ((p.R.toCx3 p.F).jR t).map_sub (eV0 p t y') (eV0 p t (((p.P.A3.A.fam.R t).zE (p.P.A3.A.fam.lvl p.P.P0 p.P.ψ0)
      ((p.R.toCx3 p.F).zs.Z t)).mulVec (((Df p).Pq t).mulVec y)))
  erw [h2, map_sub] at h
  exact sub_eq_zero.mp h
end GlobalTheory.BigTop.Fun
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieTwRecOf
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT
namespace Formalism.L2.Top4
open Formalism.L2.Top3
section StageB
abbrev SelectionBundle (𝒜 : FamClass) (sel : _root_.Formalism.L2.TwistSelection 𝒜) (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel) (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel) (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel) (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    _root_.Formalism.IndefR.RealTBAlt ((sel Fm hc).2 x hx h i) (selP Fm hc x hx h i).1 (selC Fm hc x hx h i).c.face (selC Fm hc x hx h i).Sp
      (_root_.Formalism.L2.Top4.IndefiniteScaleAtPoint sel selP selDH Fm hc x hx h i) (selS Fm hc x hx h i)
variable {𝒜 : FamClass} {sel : _root_.Formalism.L2.TwistSelection 𝒜} {selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel} {selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel} {selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel} {selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP}
def kernelChoiceOfSelection (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC) : _root_.Formalism.L2.Top4.KernelSelection 𝒜 sel :=
  fun Fm hc x hx h i => { Ks := (selB Fm hc x hx h i).T.Q.c.F }
def indefiniteRealisationChoiceOfSelection (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC) : _root_.Formalism.L2.Top4.IndefiniteRealisationChoice' 𝒜 sel selS selP selDH selC (_root_.Formalism.L2.Top4.kernelChoiceOfSelection selB) :=
  fun Fm hc x hx h i => (selB Fm hc x hx h i).Q
def SingleMapCondition (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x)
    (i : Fm.Ix x) : Prop :=
  ∀ j, Formalism.IndefR.FWT.OneMapRowR (selB Fm hc x hx h i).T (selB Fm hc x hx h i).Q.Rl.toRealDat (selB Fm hc x hx h i).κ
    (selB Fm hc x hx h i).v₀ (selB Fm hc x hx h i).O (Formalism.IndefR.phEff (selB Fm hc x hx h i).Q.Rl) j
end StageB
section TwPl
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX} {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem real_t_tw_pl_eq (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Q.Rl.twPl = P.S0.Tw :=
  tw_of_heq (congrArg (fun Z => P.A3.side3 P.P0 P.ψ0 Z) Q.zs) Q.s0
theorem tie_tw_rec_of_real_rec {Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks} (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q)
    (hs : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → w ∈ L.supp) : TieTwRec L P.S0.Tw := by
  intro y hy
  rw [← _root_.Formalism.L2.Top4.real_t_tw_pl_eq Q] at hy
  have h := (Qr.tw_iff (D.plEq.symm y)).1 (by simpa using hy)
  exact ⟨hs _ h, h⟩
end TwPl
end Formalism.L2.Top4
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwLevAt
section
set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp.TwConj
section Lev
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Lev
section Laws
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)} {j : Fin D.R.m}
end Laws
section Point
open Classical in
def TwLevAtAlt : Prop := _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ ρ ρ' : Setup (Fm.D x i).ntw, ρ.Good → ρ'.Good → RealPin p.R p.cG ρ →
  SameBut ρ ρ' → (Adapted p w ρ ∨ Adapted p w ρ') →
  ∃ (χ χ' : Formalism.L2.Host.HChar (Fm.D x i).host.E) (xiR xiR' : ∀ PP : Pl (Fm.D x i).host.E, (kP PP)ˣ →* ℂˣ),
    TwLev p.R.toRealDat χ ((baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ).chi)
      ((baseW (Fm.ex x hx i) w j ρ).de.Q ∪ (twW (Fm.ex x hx i) w ρ).Q) xiR ∧
    TwLev p.R.toRealDat χ' ((baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ').chi)
      ((baseW (Fm.ex x hx i) w j ρ).de.Q ∪ (twW (Fm.ex x hx i) w ρ').Q) xiR' ∧
    χ ≠ 1 ∧ χ' ≠ 1 ∧ (χ ≠ χ' ∨ (baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ).chi =
      (baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ').chi)
end Point
end GlobalTheory.BigOn.Exp.TwConj
end
end
end

