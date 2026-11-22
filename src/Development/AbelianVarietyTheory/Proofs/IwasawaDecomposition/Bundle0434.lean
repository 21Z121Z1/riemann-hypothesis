import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0179
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLocalRingQuotientPow
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSI
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0035
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0369
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0432
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0277
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0431
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0348
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsAbsIrrCharCompIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1579
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0350
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealPlaceDerivativesAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfAmpleNearFibres
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic

namespace GlobalTheory.DiagonalAmple

theorem isAmpleLB_of_cls_eq_lam {K : Type} [Field K] (B : Over (Sp K)) [GrpObj B] (hB : IsAbelianScheme B)
    {L N : LB B.left} (hL : L.IsLB) (hA : Out.RelAmple B L) (hN : N.IsLB)
    (e : cls N hN = lam (cls L hL) (𝟙 B) (𝟙 B)) : IsAmpleLB N := by
  have := hB.comm
  have hΘ := AbLaw.CubeProj.exists_gen_theta_of_isProjBy globalFns_holds K B hB
    (WtTower.isProjBy_of_relAmple B hL hA) L hL
  have h₁ := lam_mul_left hL hΘ (𝟙 B) (𝟙 B)⁻¹ (𝟙 B)
  rw [mul_inv_cancel, lam_one_left] at h₁
  have h₀ : pull (1 : B ⟶ B).left (cls L hL) = 0 := by
    have : (1 : B ⟶ B).left = B.hom ≫ η[B].left := rfl
    rw [this, pull_comp, PrimitiveOverField.pic_field (pull η[B].left (cls L hL)), map_zero]
  have h₂ : lam (cls L hL) (𝟙 B)⁻¹ (𝟙 B) = -(pull ((𝟙 B)⁻¹).left (cls L hL)) - cls L hL := by
    rw [lam, inv_mul_cancel, h₀, Over.id_left, pull_id]
    abel
  have hi : IsIso ((𝟙 B)⁻¹ : B ⟶ B) := by
    have : ((𝟙 B)⁻¹ : B ⟶ B) = GrpObj.inv := Category.id_comp _
    rw [this]; infer_instance
  have : IsIso ((𝟙 B)⁻¹ : B ⟶ B).left := inferInstanceAs (IsIso ((Over.forget _).map ((𝟙 B)⁻¹ : B ⟶ B)))
  have hL' := isAmpleLB_of_relAmple_of_isAffine B hL hA
  have hP : IsAmpleLB (L.pull ((𝟙 B)⁻¹).left) := hL'.pull_of_isAffineHom _
  refine hL'.tensor hP hN ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hN hL) hP.isLB)).1 ?_)
  rw [cls_div (LB.isLB_div hN hL) hP.isLB, cls_div hN hL, cls_pull hL, e, eq_neg_of_add_eq_zero_left h₁.symm, h₂]
  abel

variable {S : Scheme.{0}}

theorem diag_sqToBase (A : Over S) {S' : Scheme.{0}} (s : S' ⟶ S) :
    (lift (𝟙 ((Over.pullback s).obj A)) (𝟙 _)).left ≫ IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase A s =
      pullback.fst A.hom s ≫ (lift (𝟙 A) (𝟙 A)).left := by
  apply pullback.hom_ext
  · simp [IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase, IndefiniteRowSideFullHecke.ZeroSectionBase.toBase]
    erw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc]
    simp
  · simp [IndefiniteRowSideFullHecke.ZeroSectionBase.sqToBase, IndefiniteRowSideFullHecke.ZeroSectionBase.toBase]
    erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd_assoc]
    simp

theorem isAmpleLB_geometricFibre (P : PPAS S) {M : LB P.A.left} (hM : M.IsLB)
    (e : cls M hM = pull (lift (𝟙 P.A) (𝟙 P.A)).left P.c) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ S) :
    IsAmpleLB (M.pull (pullback.fst P.A.hom s)) := by
  obtain ⟨L, hL, hA, -, hc⟩ := P.isPol.2.2 Ω s
  refine isAmpleLB_of_cls_eq_lam ((Over.pullback s).obj P.A) (AbLaw.CubeGen.isAb_baseChange P.isAb s) hL hA
    (LB.isLB_pull hM _) ?_
  have h := congrArg (pull (lift (𝟙 ((Over.pullback s).obj P.A)) (𝟙 _)).left) hc
  rw [pull_lam, lift_fst, lift_snd, ← pull_comp, diag_sqToBase, pull_comp, ← e] at h
  exact h

theorem isProjOver_of_locally (A : Over S) [IsProper A.hom] {M : LB A.left} (hM : M.IsLB)
    (h : ∀ y : S, ∃ U : S.Opens, IsAffineOpen U ∧ y ∈ U ∧ IsAmpleLB (M.pull (A.hom ⁻¹ᵁ U).ι))
    (hS : IsProjOver (ShFam.Pad.toSpZ S)) : IsProjOver (ShFam.Pad.toSpZ A.left) := by
  obtain ⟨hp, H, hH⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hS
  have hA : Out.RelAmple A M := AmpleLocal.relAmple_of_locally S A M hM inferInstance inferInstance fun y => by
    obtain ⟨U, hU, hy, ha⟩ := h y
    have : IsAffine U := hU
    have : IsProper (Over.mk (A.hom ∣_ U)).hom := inferInstanceAs (IsProper (A.hom ∣_ U))
    exact ⟨U, hy, (relAmple_iff_isAmpleLB_of_isAffine (Over.mk (A.hom ∣_ U)) ha.isLB).2 ha⟩
  obtain ⟨-, N, hN⟩ := RelAmpleQProj.isProper_and_exists_isAmpleLB A hM hA hH
  have e : ShFam.Pad.toSpZ A.left = A.hom ≫ ShFam.Pad.toSpZ S := specZIsTerminal.hom_ext _ _
  have : IsProper (ShFam.Pad.toSpZ A.left) := by rw [e]; infer_instance
  exact hN.isProjOver _

end GlobalTheory.DiagonalAmple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JoinSIOnV0
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.JTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
  {R : Formalism.L2.RecT ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR R} {P : RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def JoinPin (Q : RealT R P Dcf Spf Zscf S Ks) : Prop :=
  ∃ eE : D.what₂.EE →ₗ[ℂ] Q.Rl.HE.H,
    (∀ y y', HEq y y' → eE (D.jEE (P.I.eRR y)) =
      Tw.out (s := Formalism.L2.SG.JoinSI.twQ P) (E := Q.Rl.HE.H)
        ((Formalism.L2.SG.JoinSI.cx Q).iC Q.F.cr true P.A3.A.μ0 (cpt P.A3.A.v0.embedding y'))) ∧
    ∀ hF : Formalism.L2.SG.PackageTie2.FinX S.Y, GlobalTheory.Mem.SRe.RowJ Q.Rl.toRealDat eE S.X S.inst S.G Q.tS (Formalism.L2.SG.JoinSI.jOf S hF)

theorem core {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    (Rl : RealDat3 D A3 Ks) (F : Face3 D A3) (n : ℕ) (hOk : A3.fam3.Ok3 n) (hSep : A3.fam3.TypesSep3)
    (hCh : Rl.WeakCharacterisation F) (hPrim : PrimRows3 Rl F) (hSchur : SchurAll D) (hSig : (D.sp.Y 0).SigOK)
    (Zs : DefSub A3.fam3.amb3) (hzs : (Rl.toCx3 F).zs = Zs)
    (S0 : IndefData (A3.side3 F.P0 F.ψ0 Zs)) (S1 : IndefData (A3.side3 F.P1 F.ψ1 Zs))
    (hs1 : HEq ((Rl.toCx3 F).data F.cr true) S1)
    (Dc : DefCols (A3.side3 F.P1 F.ψ1 Zs)) (hdc : F.Dc Zs = Dc) (Sp : SPer Dc) (hsp : HEq (F.Sp Zs) Sp)
    (p0 : BaseLevelRowSide D) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (RingOfIntegers D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL))
    (I : DivisionCompatibilityDataThreeSided D A3 F.P0 F.ψ0 F.P1 F.ψ1 Zs S0 S1 p0 Dc)
    (hDef : DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 Zs S0 S1 p0 C NuC I)
    (hDivR : DivRows3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 Zs S0 S1 p0 C NuC I)
    (hPt : ∀ (u : D.what₂.Word) (x : Fin (Dc.a (I.wU u)) → D.what₂.LL)
      (y : Fin ((A3.side3 F.P1 F.ψ1 Zs).nV A3.A.μ0) → D.what₂.LL),
      D.what₂.embLL (Dc.Pt (I.wU u) A3.A.μ0 x y) =
        D.what₂.perCol u (I.tup A3.A.μ0) (D.jN u (I.eNu u x)) (I.jA A3.A.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec y)))
    (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (Gd : GoodOp St) (hK : St.LevelSubgroupCharacter)
    (pw : ∀ u, PerW St hK u) (wdD : Dc.Mem → D.what₂.Word) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram)
    (hwdD : ∀ u, wdD (I.wU u) = u)
    (hSp : HEq Sp (spOf (twAt D.what₂.embLL A3.A.v0) Dc hK Gd wdD (fun x => pw (wdD x)) bR))
    (hbR : ∀ u i, HEq (bR (I.wU u) i) (D.eMu u (D.jN u (I.eNu u (Pi.single i 1)))))
    (t : GA D (D.sp.Y 0)) (c : ℝ)
    (hEv : EvalTieT (Rl.MY 0) Rl.ν0 Rl.fd0 (Rl.toRealDat.EEat (Rl.toRealDat.levR F.lv2 true)) St Gd
      (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c)
    (sEE : (Rl.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (Rl.toCx3 F).zs).Sp.HH)
    (sEEc : Tw (twAt D.what₂.embLL A3.A.v0) Rl.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (HHX St)) (κS : ℂ)
    (hsE : HEq sEE sEEc) (hκ : κS ≠ 0)
    (hsee : ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) Rl.HE.H)
      (hx : Rl.HE.e (Tw.out x) ∈ (Rl.toRealDat.EEat (Rl.toRealDat.levR F.lv2 true))),
      sEEc x = Tw.mk (twAt D.what₂.embLL A3.A.v0) (κS • sEEofTT (Rl.MY 0) Rl.ν0 Rl.fd0
        (Rl.toRealDat.EEat (Rl.toRealDat.levR F.lv2 true)) St Gd (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c
        ⟨Rl.HE.e (Tw.out x), hx⟩))
    (eE : D.what₂.EE →ₗ[ℂ] Rl.HE.H)
    (hRead : ∀ y y', HEq y y' → eE (D.jEE (I.eRR y)) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := Rl.HE.H)
      ((Rl.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y'))) :
    ∃ (Rd : GlobalTheory.Mem.SJ.Read D (Rl.toCx3 F) F.fc (twAt D.what₂.embLL A3.A.v0)) (M : GlobalTheory.Mem.SJ.Seam Rd F.cr),
      HEq Rd.wU I.wU ∧ M.ChainTie ∧ M.GoodPartHasComplexCoordinates ∧ M.RowTie (F.eV (Rl.toCx3 F).zs) ∧ M.ColNorm ∧
      (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ ∧
      ∀ (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St Gd) (v₀ : (Rl.MY 0).Vec) (a : ℂ),
        (∀ x, ((j x : EEC St Gd) : L2X St) =ᵐ[muX St]
          fun g => a * ev (Rl.MY 0) v₀ (Rl.HE.e (eE x)) ((Formalism.L2.SG.RowsJoinPinned.iotaX St h).symm g * t)) →
        ∀ u, ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (x : D.what₂.EE) (φ : D.what₂.Mu u) (T' : Cu St u hK),
          colDictL St (pw u).Tr hK T' = ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) →
          ⟪sEE (M.eR x), (F.fc (Rl.toCx3 F).zs).Sp.Pu (Rd.wU u)
              (GlobalTheory.Mem.SJ.cjv (twAt D.what₂.embLL A3.A.v0) (M.cφ u φ))⟫_ℂ =
            cj (twAt D.what₂.embLL A3.A.v0) (κ * ⟪((conjHH St Gd (j x) : HHX St) : L2X St), PuFun St u hK (pw u).Dt T'⟫_ℂ) := by
  subst hzs
  subst hdc
  obtain rfl := eq_of_heq hs1
  obtain rfl := eq_of_heq hsp
  obtain ⟨Rd, M, hw, h1, h2, h3, h4, hon, hT⟩ :=
    GlobalTheory.T.kernel_join_on_V0_three D G Pl0 I0 T A3 Ks Rl F n hOk hSep hCh hPrim hSchur hSig S0 p0 C NuC I hDef hDivR hPt
  exact ⟨Rd, M, hw, h1, h2, h3, h4, hon, fun j v₀ a hj => hT St h Gd hK pw wdD bR hwdD (eq_of_heq hSp) hbR t c hEv
    sEE sEEc κS hsE hκ hsee eE (fun y => hRead y y HEq.rfl) j v₀ a hj⟩

theorem bR_heq (Q : RealT R P Dcf Spf Zscf S Ks) (hPin : RealPins Q) (u : D.what₂.Word) (i : Fin (P.Dc.a (P.I.wU u))) :
    HEq (Q.bR (P.I.wU u) i) (D.eMu u (D.jN u (P.I.eNu u (Pi.single i 1)))) := by
  refine HEq.trans (heq_of_eq (hPin.bR_read (P.I.wU u) i)) ?_
  have key : ∀ (w : D.what₂.Word) (hw : w = u) (hc : P.Dc.a (P.I.wU u) = P.Dc.a (P.I.wU w)),
      HEq (D.eMu w (D.jN w (P.I.eNu w (Pi.single (Fin.cast hc i) 1))))
        (D.eMu u (D.jN u (P.I.eNu u (Pi.single i 1)))) := by
    intro w hw hc
    subst hw
    rfl
  exact key _ (Q.wdD_wU u) _

end GlobalTheory.Mem.JTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftAutEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

theorem liftAutEq : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LiftAutEq D := by
  intro hP D θ hθ ψ hψ V W χ χ' ha om hom μ 𝓕 hq Φ F hF
  obtain ⟨omO, H, e⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO_of_rank_eq D ψ hψ V W χ χ' om ha hom
  obtain ⟨E, -, -, hE, -, -, -, h7, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W ha.1.le
  have hf := (h7 ψ Φ.1).2 (mem_ThS.1 Φ.2)
  simp only [hE] at hf
  have e' : ∀ g h, (om (g, h) Φ).1 0 = thKer ψ V W omO ⟨fun x => Φ.1 (toTWsmall V W x), hf⟩ g h := fun g h => by
    have := congrFun (e (g, h) Φ) 0
    rw [toTWsmall_zero] at this
    exact this.symm
  simp only [e']
  exact (isKerSys_thKer hθ hψ (GlobalTheory.Ker.isWeak_of_datum H) H.om_cont).lift hP hθ hq hF _

end GlobalTheory.Mem.Lift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceHeckeOperatorEigenvalueConjSphericalStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_hecke_operator_eigenvalue_conj_spherical : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ J : Subgroup (GAf L n),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) →
    ∀ (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L))) (α : Fin n → ℂˣ),
    GlobalTheory.SmGL.HasSatake σ.ρ α →
    ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L), Continuous i →
    (∀ x : L, i ((GlobalTheory.HeckeFrob.conjSplit s).i x) = algebraMap L ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) x) →
    ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (T : σ.V →ₗ[ℂ] (GAf L n → W)),
    GlobalTheory.HeckeFrob.IsLocMap (GlobalTheory.HeckeFrob.conjSplit s) σ i T →
    ∀ e ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KO ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) (Fin n)),
    ∀ k, 1 ≤ k → k ≤ n →
      ((normV (GlobalTheory.HeckeFrob.conjSplit s).w : ℕ) : ℂ) ^ (k * (k - 1) / 2) • NG.tN J s ϖ k (T e) =
        (GlobalTheory.HeckeFrob.twEig (GlobalTheory.HeckeFrob.conjSplit s).w α).esymm k • T e := by
  first | exact @GlobalTheory.HeckeEigConj.tN_eig | exact GlobalTheory.HeckeEigConj.tN_eig | (intros; apply GlobalTheory.HeckeEigConj.tN_eig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StabRatInjective
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

namespace GlobalTheory.Mem.R3.GamDvd

attribute [local instance] starE

section Stab

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))} (Λ : LevFam X.E X.K n SG)

def stabRat (d : DecoSet X.E n ST SG) : MulAction.stabilizer (FormG Λ) d →* autO d.1.N where
  toFun g := ⟨(g.1.1 : Sp X.E n ≃ₗ[X.E] Sp X.E n), g.1.1.2,
    congrArg (fun e : DecoSet X.E n ST SG => e.1.N) ((MulAction.mem_stabilizer_iff).1 g.2)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem stabRat_injective (d : DecoSet X.E n ST SG) : Function.Injective (stabRat Λ d) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hγ : (g.1.1 : Sp X.E n ≃ₗ[X.E] Sp X.E n) = 1 := congrArg Subtype.val hg
  have hbe := congrArg (fun e : DecoSet X.E n ST SG => e.1.be) ((MulAction.mem_stabilizer_iff).1 g.2)
  have hM : ∀ w : SG, ((g.1.2 : GLG X.E n SG) w : Matrix (Fin n) (Fin n) (𝓞 X.E ⧸ w.1.asIdeal)) = 1 := by
    intro w
    refine Matrix.ext_of_mulVec_single fun i => ?_
    obtain ⟨x, -, hx⟩ := d.2.be_surj w (Pi.single i 1)
    have e := congrFun (congrFun hbe w) x
    change ((g.1.2 : GLG X.E n SG) w : Matrix (Fin n) (Fin n) _).mulVec
      (d.1.be w ((g.1.1 : Sp X.E n ≃ₗ[X.E] Sp X.E n).symm x)) = d.1.be w x at e
    rw [hγ] at e
    change ((g.1.2 : GLG X.E n SG) w : Matrix (Fin n) (Fin n) _).mulVec (d.1.be w x) = d.1.be w x at e
    rw [hx] at e
    rw [e, Matrix.one_mulVec]
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext hγ
  · exact Subtype.ext (funext fun w => Units.ext (hM w))

theorem card_stab_dvd (d : DecoSet X.E n ST SG) :
    Nat.card (MulAction.stabilizer (FormG Λ) d) ∣ Nat.card (autO d.1.N) :=
  Subgroup.card_dvd_of_injective (stabRat Λ d) (stabRat_injective Λ d)

end Stab

section Fam

variable {B : Base} {px : PreX B.toPre} (I : TC B px) (hX : B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc B px → B.LL))
  (tr : TrI B px)

theorem gamDvd_DGam :
    (∀ (t : TupU I U) (c : ((famC I hX U Xg tr).A.fam.R t).S.Cl),
      Fintype.card (((famC I hX U Xg tr).A.fam.R t).S.Gam c) ∣ DGam B.fields.E B.R) ∧
    ∀ (j : Fin B.R.m) (t : TupU I U) (c : ((famC I hX U Xg tr).A.fam.L j t).S.Cl),
      Fintype.card (((famC I hX U Xg tr).A.fam.L j t).S.Gam c) ∣ DGam B.fields.E B.R := by
  refine ⟨fun t c => ?_, fun j t c => ?_⟩
  · rw [Fintype.card_eq_nat_card]
    exact (card_stab_dvd _ (Quotient.out c)).trans
      (dvd_DGam (posStar_of_ok hX) B.R (pred_mem_gamRanks B.R) (Quotient.out c).2.lat (Quotient.out c).2.uni)
  · rw [Fintype.card_eq_nat_card]
    exact (card_stab_dvd _ (Quotient.out c)).trans
      (dvd_DGam (posStar_of_ok hX) B.R (nV_mem_gamRanks B.R) (Quotient.out c).2.lat (Quotient.out c).2.uni)

theorem gamDvd (l : I.Laws) (Z : Later B (I.cols l)) :
    (∀ (t : TupU I U) (c : ((famC I hX U Xg tr).A.fam.R t).S.Cl),
      Fintype.card (((famC I hX U Xg tr).A.fam.R t).S.Gam c) ∣ ((I.rec7 l Z).mem (I.rec7 l Z).u₀).C.DGam) ∧
    ∀ (j : Fin B.R.m) (t : TupU I U) (c : ((famC I hX U Xg tr).A.fam.L j t).S.Cl),
      Fintype.card (((famC I hX U Xg tr).A.fam.L j t).S.Gam c) ∣ ((I.rec7 l Z).mem (I.rec7 l Z).u₀).C.DGam :=
  gamDvd_DGam I hX U Xg tr

theorem gamDvd_stages (Y : Stages) {px : PreX Y.B.toPre} (I : TC Y.B px) (l : I.Laws) (hC : Y.C = I.cols l) (hX : Y.B.fields.Ok)
    (U : Set I.ι) (Xg : Finset (Gc Y.B px → Y.B.LL)) (tr : TrI Y.B px) :
    (∀ (t : TupU I U) (c : ((famC I hX U Xg tr).A.fam.R t).S.Cl),
      Fintype.card (((famC I hX U Xg tr).A.fam.R t).S.Gam c) ∣ (Y.toD7.mem Y.toD7.u₀).C.DGam) ∧
    ∀ (j : Fin Y.B.R.m) (t : TupU I U) (c : ((famC I hX U Xg tr).A.fam.L j t).S.Cl),
      Fintype.card (((famC I hX U Xg tr).A.fam.L j t).S.Gam c) ∣ (Y.toD7.mem Y.toD7.u₀).C.DGam := by
  have e : (Y.toD7.mem Y.toD7.u₀).C.DGam = DGam Y.B.fields.E Y.B.R := by
    have e1 : ∀ u, (Y.toD7.mem u).C.DGam = (Y.C.mem u).C.DGam := fun _ => rfl
    rw [e1, hC]
    rfl
  rw [e]
  exact gamDvd_DGam I hX U Xg tr

end Fam

end GlobalTheory.Mem.R3.GamDvd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SwapCastEqSwapAE
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtId

variable {D : D7}

theorem idFrame_iff_unitFr {V : HSp D} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V V.rank) :
    GlobalTheory.MtRead.IdFrame hF P ↔ GlobalTheory.MtIn.UnitFr P := by
  constructor
  · rintro ⟨hn, h⟩ κ
    refine Units.ext (Matrix.ext fun a b => ?_)
    have := (RingEquiv.eq_symm_apply _).1 (h κ a b)
    exact this
  · intro h
    refine ⟨rfl, fun κ a b => (RingEquiv.eq_symm_apply _).2 ?_⟩
    exact congrArg (fun g : GL (Fin V.rank) (EAf D) => g.val a b) (h κ)

def castFr {V : HSp D} {n : ℕ} (hn : V.rank = n) (P : principalLevelFrame.RowPsi V V.rank) : principalLevelFrame.RowPsi V n := hn ▸ P

theorem idFrame_castFr {V : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (hn : V.rank = n)
    {P : principalLevelFrame.RowPsi V V.rank} (h : GlobalTheory.MtIn.UnitFr P) : GlobalTheory.MtRead.IdFrame hF (castFr hn P) := by
  subst hn
  exact (idFrame_iff_unitFr hF P).2 h

end GlobalTheory.MtId

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesEqMassesOfUnfold
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.VolMass

theorem volumes_eq_masses_of_unfold :
    (∀ D : D7, StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D) → ∀ D : D7, Formalism.L2.Theta.VolTieG D → StandardLattice.VolumeEqMass₂ D :=
  fun hU D hV =>
    have hT : StandardLattice.VolTie D := Formalism.L2.Theta.VolTieG.volTie hV
    StandardLattice.volume_eq_mass_of_definite D (StandardLattice.volumeMass_of_unfolding D (hU D hT))
      (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.mass_volume_identity_of_class_decomp D hT (GlobalTheory.genusMassStd_all D)
        (GlobalTheory.DefiniteDecompObj.doubleCosets_mass D))

end GlobalTheory.Mem.VolMass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumFixesLatticeVacuaAtInertPlacesStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_datum_fixes_lattice_vacua_at_inert_places : ∀ D : D7, Formalism.IndefR.WeilFull.InertAllO D := by
  first | exact @GlobalTheory.InertAll.inertAllO | exact GlobalTheory.InertAll.inertAllO | (intros; apply GlobalTheory.InertAll.inertAllO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealPlaceDerivativesAddStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_realPlaceDerivatives_add : ∀ (D : D7) (V W : HSp D) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ X ∈ lieAt V τ, ∀ Y ∈ lieAt W τ, ∀ F F₁ F₂ : WO V W → ℂ, IsThetaFunO ψ V W F → (∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) F z) (F₁ z) 0) → (∀ z, HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) F z) (F₂ z) 0) → ∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, oneP θ W τ Y t) F z) (F₁ z + F₂ z) 0 := by
  first | exact @GlobalTheory.Mem.LieSum.hasDerivAt_add | exact GlobalTheory.Mem.LieSum.hasDerivAt_add | (intros; apply GlobalTheory.Mem.LieSum.hasDerivAt_add <;> assumption)
end

