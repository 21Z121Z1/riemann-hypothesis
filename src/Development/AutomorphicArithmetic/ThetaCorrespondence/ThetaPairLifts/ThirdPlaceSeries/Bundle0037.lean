import Formalism.LocalToGlobal.IndefiniteReal.TrISepWith
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0291
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0895
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0002
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0310
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0314
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0026

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
def pwOf_alt {Rc : _root_.Formalism.L2.RecTAlt ex} (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc)
    (hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH S.X u S.Y.hK) (u : D.what₂.Word) : Formalism.IndefR.Cx.PerW S.X S.Y.hK u where
  Dt := S.Y.Dt u
  hD := S.Y.reps u
  hin := hin u
  hlin := Formalism.L2.SG.Closed.PuLinearC_holds D S.X S.Y u
  F := (Rc.T.cols.forms u).to0
  Tr := S.tr u
  hI := S.into u
  hB := S.bij u
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure IndefiniteRealisation (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs))
    (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3)
    (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] : Type 1 where
  Rl : RealDat3 D P.A3 Ks
  sEE : (Rl.toCx3 (faceT P Dcf Spf Zscf)).EE →ₗ⋆[ℂ] ((faceT P Dcf Spf Zscf).fc (Rl.toCx3 (faceT P Dcf Spf Zscf)).zs).Sp.HH
  charW : Rl.WeakCharacterisation (faceT P Dcf Spf Zscf)
  zs : (Rl.toCx3 (faceT P Dcf Spf Zscf)).zs = P.Zs
  s0 : HEq ((Rl.toCx3 (faceT P Dcf Spf Zscf)).data (faceT P Dcf Spf Zscf).cr false) P.S0
  s1 : HEq ((Rl.toCx3 (faceT P Dcf Spf Zscf)).data (faceT P Dcf Spf Zscf).cr true) P.S1
  dc : Dcf P.Zs = P.Dc
  sp : HEq (Spf P.Zs) P.Sp
  col : HEq ((Rl.toCx3 (faceT P Dcf Spf Zscf)).colOf (faceT P Dcf Spf Zscf).cr
      ((Rl.toCx3 (faceT P Dcf Spf Zscf)).colDef
        (fun u t => (zetaEps (Rl.toCx3 (faceT P Dcf Spf Zscf)) (faceT P Dcf Spf Zscf).cr sEE u t)⁻¹) sEE)) P.C
  allPlaces : Rl.AllPlaces
  trSem : (∃ tr, Rl.TrISem (faceT P Dcf Spf Zscf) tr ∧ TrISepWith P.A3 tr) →
    Rl.TrISem (faceT P Dcf Spf Zscf) P.A3.trI ∧ P.A3.fam3.TrISep
  stdChar : Formalism.L2.Theta.IsStdChar D Rl.ψ (-1)
  psiPin : Rl.ψ = Rc.T.theta.W.ψ
  signs : Formalism.IndefR.Mi.SignsAtG Rl.toRealDat (faceT P Dcf Spf Zscf).lv2
  wdD : P.Dc.Mem → D.what₂.Word
  wdD_wU : ∀ u, wdD (P.I.wU u) = u
  wU_wdD : ∀ x, P.I.wU (wdD x) = x
  hin : ∀ u, Formalism.L2.SG.PoincareInHH.PoincareSetting.InHH S.X u S.Y.hK
  bR : ∀ x, Fin (P.Dc.a x) → (D.mem (wdD x)).A.Mram
  spPin : HEq P.Sp (Formalism.IndefR.Cx.spOf (X := S.X) (twAt D.what₂.embLL P.A3.A.v0) P.Dc S.Y.hK S.G wdD (fun x => _root_.Formalism.IndefR.pwOf_alt S hin (wdD x)) bR)
  frames : Formalism.IndefR.Seed.Frm.FramesExistDiagonal D Rl.Pg → Formalism.IndefR.Mi.FramesOKg2 Rl
  cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd
  Sx : Formalism.IndefR.NX.RatDat D.ntw
  nexp : Formalism.IndefR.NX.NExpRealS Rl cG Sx
  stdV : ∀ i, (∀ a b, (Vc D i).hT ((Vc D i).frame a) ((Vc D i).frame b) = if a = b then 1 else 0) ∧
    (Vc D i).L0 = Submodule.span (𝓞 D.host.E) (Set.range (Vc D i).frame)
  stdX : (∀ a b, D.sp.X'.hT (D.sp.X'.frame a) (D.sp.X'.frame b) = if a = b then 1 else 0) ∧
    D.sp.X'.L0 = Submodule.span (𝓞 D.host.E) (Set.range D.sp.X'.frame)
  tS : Formalism.L2.Theta.GA D (Yc D 0)
  cS : ℝ
  κS : ℝ
  ιS : Formalism.L2.Theta.GA D (Yc D 0) ≃* S.X.B.I.GA
  instEq : S.X.B.I = Formalism.IndefR.RationalEmbedding.inst D
  ιS_eq : HEq ιS (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv
  sEEc : Tw (twAt D.what₂.embLL P.A3.A.v0) Rl.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL P.A3.A.v0) (Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX S.X)
  sEEj : HEq sEE sEEc
  seeLev : (∃ t' : Formalism.L2.Theta.GA D (Yc D 0), Formalism.IndefR.AutomorphicEvaluation.ConjLevel t'⁻¹ (levS _ (Rl.βY 0) (Rl.dat0 (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Formalism.IndefR.Lev.levChi _ (Rl.βY 0) (Rl.dat0 (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (ιS k))) →
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel tS⁻¹ (levS _ (Rl.βY 0) (Rl.dat0 (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Formalism.IndefR.Lev.levChi _ (Rl.βY 0) (Rl.dat0 (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (ιS k))
  seeEval : (∃ c' : ℝ, Formalism.IndefR.AutomorphicEvaluation.EvalTieT (Rl.MY 0) Rl.ν0 Rl.fd0 (Rl.toRealDat.EEat (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true)) S.X S.G ιS tS c') →
    Formalism.IndefR.AutomorphicEvaluation.EvalTieT (Rl.MY 0) Rl.ν0 Rl.fd0 (Rl.toRealDat.EEat (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true)) S.X S.G ιS tS cS
  uS : ℂ
  uS_norm : ‖uS‖ = 1
  seeDef : ∀ (x : Tw (twAt D.what₂.embLL P.A3.A.v0) Rl.HE.H) (hx : Rl.HE.e (Tw.out x) ∈ (Rl.toRealDat.EEat (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))),
    sEEc x = Tw.mk (twAt D.what₂.embLL P.A3.A.v0) ((uS * (κS : ℂ)) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (Rl.MY 0) Rl.ν0 Rl.fd0 (Rl.toRealDat.EEat (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true)) S.X S.G ιS tS cS) ⟨Rl.HE.e (Tw.out x), hx⟩)
  seeK : 0 < κS ∧ ((∃ κ' : ℝ, 0 < κ' ∧ ∀ (x : Tw (twAt D.what₂.embLL P.A3.A.v0) Rl.HE.H) (hx : Rl.HE.e (Tw.out x) ∈ (Rl.toRealDat.EEat (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))),
      ‖(κ' : ℂ) • (Formalism.IndefR.AutomorphicEvaluation.sEEofTT (Rl.MY 0) Rl.ν0 Rl.fd0 (Rl.toRealDat.EEat (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true)) S.X S.G ιS tS cS) ⟨Rl.HE.e (Tw.out x), hx⟩‖ = ‖x‖) →
    ∀ (x : Tw (twAt D.what₂.embLL P.A3.A.v0) Rl.HE.H), Rl.HE.e (Tw.out x) ∈ (Rl.toRealDat.EEat (Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true)) →
      RealDat.nP (faceT P Dcf Spf Zscf).lv2 true * ‖sEEc x‖ ^ 2 = ‖x‖ ^ 2)
  host : HostHyp D
  err_eq : ∀ w j, ((Rl.toCx3 (faceT P Dcf Spf Zscf)).data (faceT P Dcf Spf Zscf).cr false).err0 w j =
    errCan ((Rl.toCx3 (faceT P Dcf Spf Zscf)).data (faceT P Dcf Spf Zscf).cr false)
      ((faceT P Dcf Spf Zscf).fc (Rl.toCx3 (faceT P Dcf Spf Zscf)).zs).Z.F0 w
  vpos : ∀ i, (Vc D i).IsPosDef
namespace RealT
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (R : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks)
abbrev _root_.Formalism.IndefR.IndefiniteRealisation.F (_R : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Face3 D P.A3 := faceT P Dcf Spf Zscf
def _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx : Prop := Formalism.IndefR.Seed.Frm.FramesExistDiagonal D R.Rl.Pg
end RealT
end Formalism.IndefR
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IpCEqSum
section
set_option synthInstance.maxHeartbeats 200000

section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.MiTop.CenIsom
variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word}
open Formalism.MainNotions Formalism.L2 Formalism.L2.DIV
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {R : _root_.Formalism.L2.RecTAlt ex}
set_option maxHeartbeats 1000000 in
theorem ipC_colDictL_eq_sum_inner_shP (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (hF : Formalism.L2.SG.PackageTie2.FinX S.Y) (u : D.what₂.Word)
    (T T' : Cu S.X u S.Y.hK) :
    (D.fm u).ipC 0 (colDictL S.X (S.tr u) S.Y.hK T) (colDictL S.X (S.tr u) S.Y.hK T') =
      ∑ ρ, ⟪shP S.X u T'.1 ((S.Y.cs u).h ρ), shP S.X u T.1 ((S.Y.cs u).h ρ)⟫_ℂ := by
  have h1 : ∀ P : Cu S.X u S.Y.hK, colDictL S.X (S.tr u) S.Y.hK P = (D.s_Cu u (((S.hI hF).eCu u).symm P)).1 := by
    intro P
    have h := S.colPin hF u (((S.hI hF).eCu u).symm P)
    have h' : @Eq (Cu S.X u S.Y.hK) ((S.hI hF).eCu u (((S.hI hF).eCu u).symm P)) P :=
      ((S.hI hF).eCu u).apply_symm_apply P
    exact congrArg Subtype.val ((congrArg (colDict S.X (S.tr u) S.Y.hK (S.into u) (S.bij u)) h').symm.trans h)
  have h2 := ((S.hI hF).eCu u).symm.inner_map_map T T'
  have h3 : @inner ℂ (Formalism.L2.SG.PackageTie2.ColT (hF.shInj u)) _ T T' =
      ∑ ρ, ⟪shP S.X u T'.1 ((S.Y.cs u).h ρ), shP S.X u T.1 ((S.Y.cs u).h ρ)⟫_ℂ :=
    (Formalism.L2.SG.PackageTie2.inner_colT (hF.shInj u) T T').trans (PiLp.inner_apply _ _)
  have h4 := (congrArg₂ ((D.fm u).ipC 0) (h1 T) (h1 T')).trans (D.s_Cu_isom u _ _).symm
  exact h4.trans (h2.trans h3)
theorem ipC_colDictL_rtr_eq (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (hF : Formalism.L2.SG.PackageTie2.FinX S.Y) (u : D.what₂.Word)
    (δ : Hfin S.X u) (hδ : ∀ k : Hfin S.X u, δ * k = k * δ) (T T' P P' : Cu S.X u S.Y.hK)
    (hP : P.1 = rtr S.X δ T.1) (hP' : P'.1 = rtr S.X δ T'.1) :
    (D.fm u).ipC 0 (colDictL S.X (S.tr u) S.Y.hK P) (colDictL S.X (S.tr u) S.Y.hK P') =
      (D.fm u).ipC 0 (colDictL S.X (S.tr u) S.Y.hK T) (colDictL S.X (S.tr u) S.Y.hK T') := by
  refine (_root_.GlobalTheory.MiTop.CenIsom.ipC_colDictL_eq_sum_inner_shP S hF u P P').trans (Eq.trans ?_ (_root_.GlobalTheory.MiTop.CenIsom.ipC_colDictL_eq_sum_inner_shP S hF u T T').symm)
  rw [hP, hP']
  exact sum_inner_rieszVector_rightTranslate S.Y.hK _ (S.Y.colReps u) δ hδ T T'
end GlobalTheory.MiTop.CenIsom
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTameMuPlGw
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.PendOf.isTame_reading_mu_at_split_plGw : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu := by
  intro hL D P S hS i k v hw
  have hj := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hjj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hc := hS.mu i _ hw j hjj
  have hc' : IsComp (P.tp.tup (D.nd.mu i) j) (D.naut.plGw k v) ((P.tp.tup (D.nd.mu i) j).loc (D.naut.plGw k v)) :=
    ⟨GlobalTheory.HeckeComp.smooth_loc _ _, fun _ => rfl⟩
  rw [GlobalTheory.HeckeComp.eq_of_isComp hc' hc]
  exact GlobalTheory.MuTameQS.isTame_loc (GlobalTheory.MuTameQS.tameAt_mul ((P.cf.isMu0 j).tame _) (P.tp.xi_tame _ _))
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MapMemISupIsLinAt
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum GlobalTheory.ThetaLoc
variable {D : D7} {V W : Formalism.BasicNotions.TH.HSp D}
  (om : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W →* Module.End ℂ (WO V W → ℂ))
  {TauV Fm C : Type} [AddCommGroup TauV] [Module ℂ TauV]
  [AddCommGroup Fm] [Module ℂ Fm] [AddCommGroup C] [Module ℂ C]
  (fV : Fm →ₗ[ℂ] (Formalism.L2.Theta.GA D V → TauV)) (yv : C →ₗ[ℂ] (Formalism.L2.Theta.GA D W → ℂ))
  (νV : Measure (Formalism.L2.Theta.GA D V)) (𝓕V : Set (Formalism.L2.Theta.GA D V)) (νW : Measure (Formalism.L2.Theta.GA D W)) (𝓕W : Set (Formalism.L2.Theta.GA D W))
variable (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) {G : Type} [Monoid G] (ω : G →* Module.End ℂ (WO V W → ℂ))
end GlobalTheory.ThetaTri
end
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum GlobalTheory.ThetaLoc
variable {D : D7} {V W : Formalism.BasicNotions.TH.HSp D}
  (om : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W →* Module.End ℂ (WO V W → ℂ))
  {TauV Fm C : Type} [AddCommGroup TauV] [Module ℂ TauV]
  [AddCommGroup Fm] [Module ℂ Fm] [AddCommGroup C] [Module ℂ C]
  (fV : Fm →ₗ[ℂ] (Formalism.L2.Theta.GA D V → TauV)) (yv : C →ₗ[ℂ] (Formalism.L2.Theta.GA D W → ℂ))
  (νV : Measure (Formalism.L2.Theta.GA D V)) (𝓕V : Set (Formalism.L2.Theta.GA D V)) (νW : Measure (Formalism.L2.Theta.GA D W))
  (𝓕W : Set (Formalism.L2.Theta.GA D W)) (c : ℂ)
variable (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) {G : Type} [Monoid G]
  (ω : G →* Module.End ℂ (WO V W → ℂ))
end GlobalTheory.ThetaTri
end
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ThetaLoc
open scoped TensorProduct
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}
def eWloc_alt (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) : (X.R.cV j).W ≃ₗ[ℂ] (P.M.loc i).wt.W := by
  have key : ∀ (k : ℕ) (hk : j.1 + 1 = k) (p1 : 1 ≤ k) (p2 : k ≤ D.R.m),
      (X.R.cV j).W ≃ₗ[ℂ] (P.M (D.nd.mu i) k p1 p2).wt.W := by
    rintro k rfl p1 p2
    exact A.eW _ hμ j
  exact key _ hj _ _
def formToVectorMap (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) :
    ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) →ₗ[ℂ] (Formalism.L2.Theta.GA D (Vc D j) → (X.R.cV j).W) :=
  (X.R.cV j).ext ∘ₗ
    { toFun := fun F k => (_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm
        ((F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) (A.a j * preF (A.PV j) k))
      map_add' := fun F F' => by funext k; simp
      map_smul' := fun c F => by funext k; simp }
def canonicalEmbedding' {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) :
    Y.A →ₗ[ℂ] Formalism.IndefR.Mult.MMap (X.R.MW j (sg0 D X.A)) :=
  Classical.choose hc
def canonicalConstant {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) : ℝ :=
  Classical.choose (Classical.choose_spec hc)
def thetaEvaluationMap {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) :
    ↥Y.C →ₗ[ℂ] (Formalism.L2.Theta.GA D (Wc D j) → ℂ) :=
  LinearMap.applyₗ (PiTensorProduct.map (fun τ => (lowT (X.R.MW j (sg0 D X.A)) τ).subtype)
      (kUnit (X.R.MW j (sg0 D X.A)))) ∘ₗ
    (PiTensorProduct.lift : Formalism.IndefR.Mult.MMap (X.R.MW j (sg0 D X.A)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ _root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc ∘ₗ Y.C.subtype
def standardWeilRepresentation (A : GlobalTheory.NJoin.Agree X P.M P.rep) (j : Fin D.R.m) (t : X.T) :
    GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ (WO (Vc D j) (Wc D j) → ℂ) :=
  (X.R.ωP j t).comp ((A.PV j).ψ.prodMap (X.PW j).ψ)
def OmegaSubmoduleAtLocal (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    {Y : RowMod D P.rep (D.nd.j i)} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) :
    Submodule ℂ ((X.R.cV j).W →ₗ[ℂ] (WO (Vc D j) (Wc D j) → ℂ)) :=
  OmSub (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ) (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc) (X.R.νV j (X.tupT (D.nd.mu i)))
    (X.R.fdV j (X.tupT (D.nd.mu i))) (X.R.νW j) (X.R.fdW j) X.R.ψ
    (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i)))
def canonicalPairingValue (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    {Y : RowMod D P.rep (D.nd.j i)} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i))
    (φ : (X.R.cV j).W →ₗ[ℂ] (WO (Vc D j) (Wc D j) → ℂ))
    (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) (y : ↥Y.C) : ℂ :=
  lamV (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ) (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc) (X.R.νV j (X.tupT (D.nd.mu i)))
    (X.R.fdV j (X.tupT (D.nd.mu i))) (X.R.νW j) (X.R.fdW j) (_root_.GlobalTheory.ThetaTri.canonicalConstant hc : ℂ) φ F y
def standardSchwartzFunctionMap (j : Fin D.R.m) (t : X.T) : (X.R.cV j).W →ₗ[ℂ] (WO (Vc D j) (Wc D j) → ℂ) :=
  pureTensorO X.R.ψ X.R.θ (Vc D j) (Wc D j) (fun _ => 1) (cart (X.R.MW j (sg0 D X.A))) (X.R.BV j)
    (onb (X.R.MW j (sg0 D X.A))) (X.R.vP j t) ∘ₗ X.R.ioP j (kUnit (X.R.MW j (sg0 D X.A)))
end GlobalTheory.ThetaTri
end
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum GlobalTheory.ThetaLoc
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n r : ℕ}
theorem map_mem_iSup_range_isLinAt {Θ Ω : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup Ω] [Module ℂ Ω]
    (ω₁ : GAf E n × GAf E r →* Module.End ℂ Θ) (ω₂ : GAf E n × GAf E r →* Module.End ℂ Ω)
    (P : Θ → Prop) (Q : Ω → Prop) (T : Θ →ₗ[ℂ] Ω) (hT : ∀ p f, P f → T (ω₁ p f) = ω₂ p (T f))
    (hTQ : ∀ f, P f → Q (T f)) (s : SplitPlace E) (μ η : (s.w.adicCompletion E)ˣ →* ℂˣ) {f : Θ}
    (hf : f ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Θ)
      (_ : IsLinAt ω₁ s μ η ι ∧ ∀ Φ, P (ι Φ)), LinearMap.range ι) :
    T f ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Ω)
      (_ : IsLinAt ω₂ s μ η ι ∧ ∀ Φ, Q (ι Φ)), LinearMap.range ι := by
  have hle : (⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Θ)
      (_ : IsLinAt ω₁ s μ η ι ∧ ∀ Φ, P (ι Φ)), LinearMap.range ι).map T ≤
      ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Ω)
      (_ : IsLinAt ω₂ s μ η ι ∧ ∀ Φ, Q (ι Φ)), LinearMap.range ι := by
    rw [Submodule.map_iSup]
    refine iSup_le fun ι => ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun hι => ?_
    rw [← LinearMap.range_comp]
    exact le_iSup₂_of_le (T ∘ₗ ι) ⟨isLinAt_comp ω₁ ω₂ P T hT s μ η ι hι.2 hι.1, fun Φ => hTQ _ (hι.2 Φ)⟩ le_rfl
  exact hle (Submodule.mem_map_of_mem hf)
theorem mem_iSup_range_isLinAt_valAct1 {Θ B : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup B] [Module ℂ B]
    [FiniteDimensional ℂ B] (ω : GAf E n × GAf E r →* Module.End ℂ Θ) (P : Θ → Prop) (Q : (B →ₗ[ℂ] Θ) → Prop)
    (hQ : ∀ β f, P f → Q (single1 β f))
    (s : SplitPlace E) (μ η : (s.w.adicCompletion E)ˣ →* ℂˣ) (φ : B →ₗ[ℂ] Θ)
    (hφ : ∀ b, φ b ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Θ)
      (_ : IsLinAt ω s μ η ι ∧ ∀ Φ, P (ι Φ)), LinearMap.range ι) :
    φ ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] (B →ₗ[ℂ] Θ))
      (_ : IsLinAt (valAct1 ω) s μ η ι ∧ ∀ Φ, Q (ι Φ)), LinearMap.range ι := by
  let bB := Module.finBasis ℂ B
  rw [eq_sum_single1 bB φ]
  refine Submodule.sum_mem _ fun l _ => ?_
  exact _root_.GlobalTheory.ThetaTri.map_mem_iSup_range_isLinAt ω (valAct1 ω) P Q (single1 (bB.coord l))
    (fun p f _ => single1_valAct1 ω _ p f) (fun f hf => hQ _ f hf) s μ η (hφ _)
variable {D : D7} {V W : Formalism.BasicNotions.TH.HSp D}
  (om : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W →* Module.End ℂ (WO V W → ℂ))
  {TauV Fm C : Type} [AddCommGroup TauV] [Module ℂ TauV]
  [AddCommGroup Fm] [Module ℂ Fm] [AddCommGroup C] [Module ℂ C]
  (fV : Fm →ₗ[ℂ] (Formalism.L2.Theta.GA D V → TauV)) (yv : C →ₗ[ℂ] (Formalism.L2.Theta.GA D W → ℂ))
  (νV : Measure (Formalism.L2.Theta.GA D V)) (𝓕V : Set (Formalism.L2.Theta.GA D V)) (νW : Measure (Formalism.L2.Theta.GA D W))
  (𝓕W : Set (Formalism.L2.Theta.GA D W)) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ)
  (ω : GAf E n × GAf E r →* Module.End ℂ (WO V W → ℂ))
end GlobalTheory.ThetaTri
end
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ThetaLoc
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}
def omegaMapAtLocal (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    {Y : RowMod D P.rep (D.nd.j i)} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) :
    GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ ↥(_root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ) :=
  omSub (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ) (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc) (X.R.νV j (X.tupT (D.nd.mu i)))
    (X.R.fdV j (X.tupT (D.nd.mu i))) (X.R.νW j) (X.R.fdW j) X.R.ψ (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i)))
def canonicalPairingMap (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    {Y : RowMod D P.rep (D.nd.j i)} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) :
    ↥(_root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ) →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) →ₗ[ℂ] ↥Y.C →ₗ⋆[ℂ] ℂ :=
  lam (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ) (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc) (X.R.νV j (X.tupT (D.nd.mu i)))
    (X.R.fdV j (X.tupT (D.nd.mu i))) (X.R.νW j) (X.R.fdW j) (_root_.GlobalTheory.ThetaTri.canonicalConstant hc : ℂ) X.R.ψ (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i)))
end GlobalTheory.ThetaTri
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.NFacts
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
structure CoreNormFacts (D : D7) : Prop where
  what₂ : _root_.GlobalTheory.NRows.PointConditions' D
  adm : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D
  Conclusion1 : _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D
  Conclusion2 : SumRepresentations.Conclusion2 D
  rhoBar : ResidualIrreducibleRankR D
  g3p : _root_.UpperTheory.GalS.AdmissibleResidualTameEigenvalues D
  weight : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D
  block : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D
  g2 : _root_.Formalism.MainNotions.AdmissibleParameterJ.DeRhamFamilyAwayAlt D ∧ _root_.UpperTheory.GalS.DeRhamJumpsDistinctCondition D
  admJ : ∀ L : SizeData₂ D, AdmissibleParameterJ.AdmPar L → _root_.Formalism.MainNotions.AdmissibleParameterJ.AdmJAlt L
  muUnr : GlobalTheory.HubX.MuUnr D
  depthG : GlobalTheory.HubX.DepthZeroG D
  bc : SphericalInertData.Conclusion1 D
  lam : GlobalTheory.NRows.LamUsed D
structure NormChoiceFacts (D : D7) (C : NChoice D) : Prop extends toCore : _root_.GlobalTheory.NFacts.CoreNormFacts D where
  c2 : KillingConditions.LocalisationUniqueness D
  large : GlobalTheory.CoefDuty.Large D
  duties : GlobalTheory.CoefDuty.Duties D
  nct : NChTie D C
  trip : GlobalTheory.PtCore.TriplesGood D
  same : GlobalTheory.PtCore.SameTwist D C
  good : GoodFTAll D
theorem CoreNormFacts.admA {D : D7} (h : _root_.GlobalTheory.NFacts.CoreNormFacts D) : _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D := h.adm.1.1
theorem CoreNormFacts.a3 {D : D7} (h : _root_.GlobalTheory.NFacts.CoreNormFacts D) (L : SizeData₂ D) : TwistedPlaces.adm3 L := h.what₂.rank L
theorem CoreNormFacts.isot {D : D7} (h : _root_.GlobalTheory.NFacts.CoreNormFacts D) : Rows.IsotInternal D.what₂ := h.adm.2.2
end GlobalTheory.NFacts
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Purity
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.GalClose
open GlobalTheory.CuspRep
theorem purity_alt (hRP : GlobalTheory.Published.RegularAlgebraicPurity) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (a : ℕ) (π : D.naut.CG a) (hr : D.naut.ralg π) : ∃ w₀ : ℂ, ∀ τ : D.host.E →+* ℂ,
      D.naut.infG π (τ.comp (D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E).toRingEquiv.toRingHom) =
        (D.naut.infG π τ).map (w₀ - ·) := by
  have := host_isCMField D.host
  rcases Nat.eq_zero_or_pos a with rfl | ha1
  · haveI := P.cg.zero
    exact isEmptyElim π
  obtain ⟨π₀, hπ₀⟩ := Quotient.exists_rep (P.cg.e a π).1
  have hmk : CG.mk π₀ = (P.cg.e a π).1 := hπ₀
  have hinf : ∀ τ, D.naut.infG π τ = (CG.mk π₀).infChar τ := fun τ => by
    rw [P.cg.inf, CGu.infChar, ← hmk]
  have hr₀ : (CG.mk π₀).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have := (D.naut.ralg_def π).1 hr τ
    rwa [hinf] at this
  obtain ⟨w₀, hw⟩ := (hRP D.host.E a ha1 π₀ hr₀).1
  refine ⟨(w₀ : ℂ), fun τ => ?_⟩
  have hc : τ.comp (D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E).toRingEquiv.toRingHom = (starRingEnd ℂ).comp τ :=
    RingHom.ext fun x => GlobalTheory.SplitRowProbe.conj_sqrt D.host τ x
  rw [hc, hinf, hinf, hw]
end GlobalTheory.GalClose
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRtEqOfGoodInertStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operator_eigen_good_place_first_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.UG.IsInertAt D.host.F D.host.E (Pp.under (𝓞 D.host.F)) Pp → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))), NG.OverPl Pp v → ∀ g : D.what₂.Mt (D.nd.mu i) (D.nd.j i), ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {v} κ → NG.rt D.host.E D.R.nV κ ((P.M.loc i).real g) = (P.M.loc i).real g := by
  first | exact @_root_.GlobalTheory.InertFormFix.real_rt_eq_of_good_inert_alt | exact _root_.GlobalTheory.InertFormFix.real_rt_eq_of_good_inert_alt | (intros; apply _root_.GlobalTheory.InertFormFix.real_rt_eq_of_good_inert_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SysParamAtInertStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_eigen_compatibility_fourth_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ s : GlobalTheory.DownLift.Sys D, GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i)) → Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∃ Bw, GlobalTheory.LFun.IsSysParam D.sp.cm.sig (Formalism.IndefR.Links.Vc D j).rank (rfl : w.under (𝓞 D.host.F) = _) (s w) Bw := by
  first | exact @_root_.GlobalTheory.NJoin.sysParam_at_inert_alt | exact _root_.GlobalTheory.NJoin.sysParam_at_inert_alt | (intros; apply _root_.GlobalTheory.NJoin.sysParam_at_inert_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SysParamSplitStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_eigen_compatibility_third_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ s : GlobalTheory.DownLift.Sys D, GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) ∉ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i)) → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → ∃ Bw, GlobalTheory.LFun.IsSysParam D.sp.cm.sig (Formalism.IndefR.Links.Vc D j).rank (rfl : w.under (𝓞 D.host.F) = _) (s w) Bw := by
  first | exact @_root_.GlobalTheory.EigStr.sysParam_split_alt | exact _root_.GlobalTheory.EigStr.sysParam_split_alt | (intros; apply _root_.GlobalTheory.EigStr.sysParam_split_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ToSTiesR
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Mem.SRe
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}
def SRest.toRealSpectralMatching (Rc : _root_.Formalism.L2.RecTAlt ex) {P : SPack D fun u => (Rc.T.cols.forms u).to0} (S : SRest P) :
    _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc where
  toSTies := S.toSTies
  tr := P.tr
  into := P.into
  bij := P.bij
  lev := P.lev
  colPin := fun _ => S.colPin
  inst := P.inst
  G := P.G
  rowTie := fun _ => S.rowTie
  locTied := S.locTied
section
end
end GlobalTheory.Mem.SRe
end
end
end

