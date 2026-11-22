import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreePointHalfLevelLift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2217
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2083
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0966
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameRelationIntegerExponentSectionBaseChangeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameRelation_integerExponentSection_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y₀ : FrPt Xo c K) (e : Formalism.L2.Pj.Ix Dw → ℤ) (k : (E →+* ℂ) → ℕ),
    e none = 0 → ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, ∀ G : MvPolynomial (Formalism.L2.LamCM.FrVar Dw.mult) K,
      (∀ (y' : FrPt Xo c K) (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) K),
          (∀ b, (Y b).det ≠ 0) → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) 1 y₀ y' →
          (∏ b, (Y b).det ^ k b) * evR Xo c F y' = Formalism.L2.LamCM.evalFr G Y) →
      ∀ (S : Type) [Field S] [Algebra c.F S] (φ : K →ₐ[c.F] S) (z z' : FrPt Xo c S)
        (Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S) (s : Sˣ),
        (∀ b, (Y b).det ≠ 0) → FrMap φ y₀ z → GlobalTheory.Frames.FrChg (fun b => (Y b).transpose) (s : S) z z' →
        (∏ b, (Y b).det ^ k b) * evR Xo c F z' = Formalism.L2.LamCM.evalFr (MvPolynomial.map φ.toRingHom G) Y := by
  first | exact @GlobalTheory.FrameRelBC.relation_baseChange_field | exact GlobalTheory.FrameRelBC.relation_baseChange_field | (intros; apply GlobalTheory.FrameRelBC.relation_baseChange_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedPointVectorsVerticalDeformationEigenbasis
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole

section Chg

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.Reg GlobalTheory.FlagMod
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem frVec_of_frChg {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Type} [CommRing S]
    [Algebra c.F S] {M : MChart Y} {x : Sp S ⟶ Y.X} (h : ⊤ ≤ x ⁻¹ᵁ M.U) {P P' : FrPt Xo c S}
    (hx : frX P ≫ Y.j = x) (hx' : frX P' ≫ Y.j = x)
    {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S} {a : S} (hC : GlobalTheory.Frames.FrChg g a P P')
    (σ : E →+* ℂ) (i : Fin (Dw.mult σ)) :
    frVec Y P' hx' σ i = ∑ j, g σ i j • frVec Y P hx σ j := by
  have eX : frX P' = frX P := xF_ext (frX_snd _) (frX_snd _) (hx'.trans hx.symm)
  have e : P'.x = P.x := hC.1
  obtain ⟨Λ₀⟩ := MChart.nonempty_lift E H Dw l Xo c O β Y M S (ev x M.U h) (frX P) (frX_snd P)
    (hx.trans (spMap_ev x M.hU h).symm)
  let Λ : M.Lift (ev x M.U h) P.x := frX_fst P ▸ Λ₀
  have eΛ : Λ.xF = frX P := eq_frX P Λ.xF_fst Λ.xF_snd
  have h4 := (VecComb.isCombAt_iff_vec E H Dw l Xo c O β Y M S _ P.x Λ _
      (fun j => (vec M x h).symm (frVec Y P hx σ j)) (P.u σ) _ _ fun j =>
        (vec_iff_toModel h Λ eΛ (frX_fst P) hx _ (P.tan σ j)).2 (LinearEquiv.apply_symm_apply _ _).symm).1
      (hC.2.1 σ i)
  have h5 := (vec_iff_toModel h Λ eΛ (frX_fst P) hx _ (e ▸ P'.tan σ i)).1 h4
  rw [map_sum] at h5
  simp only [map_smul, LinearEquiv.apply_symm_apply] at h5
  rw [← h5]
  obtain ⟨u, hu⟩ := (toModel_eq_iff _ (frX_fst P') hx' (P'.tan σ i) _).1 rfl
  exact ((toModel_eq_iff _ _ _ _ _).2 ⟨u, eX ▸ hu⟩).symm

end Chg

end GlobalTheory.LogPole

namespace GlobalTheory.LogPole

attribute [local instance] Over.cartesianMonoidalCategory

theorem frVec_isVert_isCombAtG : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (K : Type) [Field K] [Algebra c.F K] (P₀ P : FrPt Xo c K) (hU : ⊤ ≤ (frX P₀ ≫ TF.Y.j) ⁻¹ᵁ U.1) (G : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K), GlobalTheory.Frames.FrChg G 1 P₀ P → IsBaseFrame TF U e v P₀ hU → ∀ (N' : GlobalTheory.FlagTan.FIx Dw → K) (w : FrPt Xo c (DualNumber K)) (x : Sp (DualNumber K) ⟶ TF.Y.X) (hx : frX w ≫ TF.Y.j = x) (hUx : ⊤ ≤ x ⁻¹ᵁ U.1) (M : GlobalTheory.Reg.MChart TF.Y) (hM : ⊤ ≤ x ⁻¹ᵁ M.U), IsVert P N' w → ∀ σ i, IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) (fun j => (GlobalTheory.FlagTan.unip K N' σ * (G σ).map (fun r => (TrivSqZeroExt.inl r : DualNumber K))) i j) (tv (frVec TF.Y w hx σ i)).left := by
  intro E _ _ _ H Dw l Xo c TF U n e v _hv K _ _ P₀ P hU G hG hB N' w x hx hUx M hM hV σ i
  obtain ⟨y₀, hy₀, hS⟩ := hV
  obtain ⟨P₀', h0⟩ := GlobalTheory.FlagTan.exists_frMap (GlobalTheory.FlagTan.cst c K) P₀
  have hC := (GlobalTheory.FlagTan.frMap_iff_frChg hG h0).1 hy₀
  have ew : frX w = frX y₀ := FlagMod.eq_frX y₀ ((FlagMod.frX_fst w).trans hS.1) (FlagMod.frX_snd w)
  have ey : frX y₀ = frX P₀' := FlagMod.eq_frX P₀' ((FlagMod.frX_fst y₀).trans hC.1) (FlagMod.frX_snd y₀)
  have hx₀ : frX y₀ ≫ TF.Y.j = x := ew ▸ hx
  have hx' : frX P₀' ≫ TF.Y.j = x := ey ▸ hx₀
  have e1 := frVec_of_frChg hM hx₀ hx hS σ i
  have e2 := fun j => frVec_of_frChg hM hx' hx₀ hC σ j
  have ecst : spMap (GlobalTheory.FlagTan.cst c K).toRingHom ≫ (frX P₀ ≫ TF.Y.j) = x := by
    rw [← Category.assoc, FlagMod.frX_frMap h0, hx']
  have eev : ev x U.1 hUx = (GlobalTheory.FlagTan.cst c K).toRingHom.comp (ev (frX P₀ ≫ TF.Y.j) U.1 hU) := by
    rw [FlagMod.ev_congr ecst.symm U.1 hUx (ecst ▸ hUx), FlagMod.ev_spMap]
  have e3 : ∀ k, (tv (frVec TF.Y P₀' hx' σ k)).left = spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, k⟩) := by
    intro k
    rw [← FlagMod.tanPull_frVec h0 rfl hx' ecst, FlagMod.tanPull_left, hB σ k, ← Category.assoc, spMap_comp',
      ← dualMap_comp, eev]
  open MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections in
  have key : frVec TF.Y w hx σ i = ∑ k, (GlobalTheory.FlagTan.unip K N' σ *
      (G σ).map (fun r => (TrivSqZeroExt.inl r : DualNumber K))) i k • frVec TF.Y P₀' hx' σ k := by
    rw [e1]
    simp_rw [e2, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_apply, Finset.sum_smul]
    rfl
  have hv' : (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) =
      fun j => (tv (frVec TF.Y P₀' hx' σ j)).left := funext fun j => (e3 j).symm
  rw [hv', GlobalTheory.LieMet.isComb_iff]
  exact key

end GlobalTheory.LogPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreePointFieldAlgebraicallyClosedStatement
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.free_point_field_algebraically_closed : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), RowsT p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (fun g : (p.F.lv2.lvl false).P => (p.O i).lev2 (g : p.P.Gp)) := by
  first | exact @GlobalTheory.DefFree.free_base | exact GlobalTheory.DefFree.free_base | (intros; apply GlobalTheory.DefFree.free_base <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreePointHalfLevelLiftStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open Formalism.IndefR.FWT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.free_point_half_level_lift : Hypotheses2 → Gram → Lifts fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ k : Fin 2,
    GlobalTheory.DefPt.FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c
      (fun h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k => (p.O i).lev2 ((p.R.eG.trans p.cG).symm (h : G0g (Fm.D x ι).nd))) := by
  first | exact @GlobalTheory.NeatOne.free_half_lifts | exact GlobalTheory.NeatOne.free_half_lifts | (intros; apply GlobalTheory.NeatOne.free_half_lifts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FstIsFinFFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StageDict

theorem fst_isFinF_frames : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (FA : GlobalTheory.ChainFr.Fr A) (FW : GlobalTheory.ChainFr.Fr WW), (∀ τ, (GlobalTheory.SquareComm.frSgn true FA).cart τ = -X.rA.s τ) →
    (∀ τ, FW.cart τ = X.rW.s τ) → X.Is ψ θ α β νH S → ∀ t, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW (X.f t) := by
  intro D T A A' WW X ψ θ α β νH S FA FW hcA hcW hX t
  have hv := hX.isVac
  have hν : Formalism.L2.Theta.IsHeckeChar D (α t / β t) := by
    have h := (hX.weil t).hecT
    rw [← inv_div]
    refine ⟨?_, fun x => ?_⟩
    · exact continuous_inv.comp h.1
    · show ((β t / α t) _)⁻¹ = 1
      rw [h.2 x, inv_one]
  have hI : X.ideal S t ≠ ⊥ := by
    unfold Tri.ideal
    rw [← Ideal.zero_eq_bot]
    refine Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ ?_
    rw [Ideal.zero_eq_bot]
    exact w.ne_bot
  obtain ⟨f₁, h1, h1t⟩ := GlobalTheory.Adopt.first_standard_pair_member_has_theta_function D ψ θ A WW X.rA X.rW (α t / β t) (X.e t) (S t) (X.ideal S t) X.vac
    hX.rigA hX.rigW hν (hX.idem t) hI hv
  have heq : X.f t = f₁ := by
    obtain ⟨⟨Tm, hT⟩, hall⟩ := hX.fst t
    rw [hall Tm hT, h1.2 Tm hT]
  have hft : IsThetaFunO ψ (GlobalTheory.Grid.neg A) WW (X.f t) := heq ▸ h1t
  refine ⟨hft, fun τ => ?_⟩
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hX.idem t)
  have hF := GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hv.1.1.1 hv.2.inf ho.infPart_eq ho.conj.infPart_eq
    (hX.fst t) hv.2.theta hft (hv.2.fock τ)
  rw [hcA τ, hcW τ]
  exact hF

end GlobalTheory.StageDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullHeckeRealDatMovedReadings
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnframePt

open GlobalTheory.RealGeo GlobalTheory.Unframe Formalism.IndefR.FWT

abbrev fullHeckeRealDatMovedReadings {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks)
    (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ) : RealDat3 D A3 Ks :=
  { Rl with toRealDat := moveR Rl.toRealDat w }

section Pt

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

def geoHalf (p : PtAt ex Csz) : GeoHalf p.T p.R.toRealDat (fun _ => 1) :=
  ⟨p.κ, p.v₀, p.fw, p.bar, p.O, p.pins, p.rhoGeo, p.equivAll, p.cTie, fun i hu => by
    have e : phEff p.R = fun _ => (1 : ℂ) := funext p.phEff_one
    rw [← e]
    exact p.phase i hu⟩

end Pt

end GlobalTheory.UnframePt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionalPosOnSquaresEqSumOfSquares
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.SumSqFunctional

open Matrix

def quadR {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ) (v : Fin r → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * (L i j : ℝ) * v j

lemma quadR_eq {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ) (v : Fin r → ℝ) :
    star v ⬝ᵥ (L.map (Int.cast : ℤ → ℝ)) *ᵥ v = quadR L v := by
  simp [quadR, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

lemma quadR_intCast {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ) (w : Fin r → ℤ) :
    quadR L (fun i => (w i : ℝ)) = ((w ⬝ᵥ L *ᵥ w : ℤ) : ℝ) := by
  simp [quadR, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]

lemma continuous_quadR {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ) : Continuous (quadR L) := by
  unfold quadR; fun_prop

lemma exists_int_multiple {r : ℕ} (q : Fin r → ℚ) :
    ∃ d : ℕ, 0 < d ∧ ∃ w : Fin r → ℤ, ∀ i, (w i : ℚ) = d * q i := by
  refine ⟨∏ i, (q i).den, Finset.prod_pos (fun i _ => (q i).den_pos), ?_⟩
  have : ∀ i, ∃ z : ℤ, (z : ℚ) = ((∏ j, (q j).den : ℕ) : ℚ) * q i := by
    intro i
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun j => (q j).den) (Finset.mem_univ i)
    refine ⟨k * (q i).num, ?_⟩
    rw [hk]; push_cast
    rw [mul_comm ((q i).den : ℚ) (k : ℚ), mul_assoc, Rat.den_mul_eq_num]
  choose w hw using this
  exact ⟨w, hw⟩

lemma quadR_pos_rat {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ)
    (hp : ∀ v : Fin r → ℤ, v ≠ 0 → 0 < v ⬝ᵥ L *ᵥ v) (q : Fin r → ℚ) (hq : q ≠ 0) :
    0 < quadR L (fun i => (q i : ℝ)) := by
  obtain ⟨d, hd, w, hw⟩ := exists_int_multiple q
  have hwR : ∀ i, (w i : ℝ) = d * (q i : ℝ) := by
    intro i; have := congrArg (Rat.cast : ℚ → ℝ) (hw i); push_cast at this; exact this
  have hw0 : w ≠ 0 := by
    intro h; apply hq; funext i
    have := hw i; rw [h] at this; simp at this
    rcases this with h1 | h1
    · exact absurd h1 (by exact_mod_cast hd.ne')
    · exact h1
  have h1 := hp w hw0
  have h2 : quadR L (fun i => (w i : ℝ)) = (d : ℝ) ^ 2 * quadR L (fun i => (q i : ℝ)) := by
    simp only [quadR, hwR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h3 : 0 < quadR L (fun i => (w i : ℝ)) := by
    rw [quadR_intCast]; exact_mod_cast h1
  rw [h2] at h3
  have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
  exact pos_of_mul_pos_right h3 hd2.le

lemma quadR_nonneg {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ)
    (hp : ∀ v : Fin r → ℤ, v ≠ 0 → 0 < v ⬝ᵥ L *ᵥ v) (x : Fin r → ℝ) : 0 ≤ quadR L x := by
  have hdense : DenseRange (Pi.map (fun (_ : Fin r) (t : ℚ) => (t : ℝ))) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hcl : IsClosed {x : Fin r → ℝ | 0 ≤ quadR L x} :=
    isClosed_le continuous_const (continuous_quadR L)
  have hsub : Set.range (Pi.map (fun (_ : Fin r) (t : ℚ) => (t : ℝ))) ⊆ {x | 0 ≤ quadR L x} := by
    rintro _ ⟨q, rfl⟩
    by_cases hq : q = 0
    · subst hq; simp [quadR]
    · exact (quadR_pos_rat L hp q hq).le
  have := hcl.closure_subset_iff.mpr hsub
  rw [hdense.closure_range] at this
  exact this (Set.mem_univ x)

theorem posDef_of_pos_int {r : ℕ} (L : Matrix (Fin r) (Fin r) ℤ) (hs : Lᵀ = L)
    (hp : ∀ v : Fin r → ℤ, v ≠ 0 → 0 < v ⬝ᵥ L *ᵥ v) :
    (L.map (Int.cast : ℤ → ℝ)).PosDef := by
  have hH : (L.map (Int.cast : ℤ → ℝ)).IsHermitian := by
    ext i j
    have := congrFun (congrFun hs j) i
    simp only [Matrix.transpose_apply] at this
    simp [Matrix.conjTranspose_apply, this]
  have hPSD : (L.map (Int.cast : ℤ → ℝ)).PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH (fun x => by
      rw [quadR_eq]; exact quadR_nonneg L hp x)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH (fun x hx => ?_)
  rw [quadR_eq]
  refine lt_of_le_of_ne (quadR_nonneg L hp x) (fun h0 => ?_)
  have hz : (L.map (Int.cast : ℤ → ℝ)) *ᵥ x = 0 := by
    rw [← hPSD.dotProduct_mulVec_zero_iff, quadR_eq]; exact h0.symm
  have hdetR : (L.map (Int.cast : ℤ → ℝ)).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx, hz⟩
  have hdet : L.det = 0 := by
    have := (Int.castRingHom ℝ).map_det L
    rw [RingHom.mapMatrix_apply] at this
    simp only [eq_intCast] at this
    have h' : ((L.det : ℤ) : ℝ) = 0 := by rw [this]; exact hdetR
    exact_mod_cast h'
  obtain ⟨w, hw, hLw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have := hp w hw
  rw [hLw, dotProduct_zero] at this
  exact lt_irrefl _ this

end GlobalTheory.Poinc.SumSqFunctional

namespace GlobalTheory.Poinc.SumSqFunctional

open Matrix

theorem sumsq_functional : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (lam : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), (∀ l : X →ₗ[ℤ] ℤ, l ≠ 0 → 0 < lam (GlobalTheory.PolFan.sqForm l)) → ∃ (D m : ℕ) (a : Fin m → X), 1 ≤ D ∧ Submodule.span ℤ (Set.range a) = ⊤ ∧ ∀ β : LinearMap.BilinForm ℤ X, (∀ x y, β x y = β y x) → ∑ i, β (a i) (a i) = (D : ℤ) * lam β := by
  intro X _ _ _ lam hpos
  let b : Module.Basis (Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ X))) ℤ X :=
    (Module.Free.chooseBasis ℤ X).reindex (Fintype.equivFin _)
  set r := Fintype.card (Module.Free.ChooseBasisIndex ℤ X)
  let C : Fin r → Fin r → LinearMap.BilinForm ℤ X := fun i j =>
    (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j)
  have hexp : ∀ β : LinearMap.BilinForm ℤ X, β = ∑ i, ∑ j, β (b i) (b j) • C i j := by
    intro β
    refine b.ext fun k => b.ext fun l => ?_
    simp [C, LinearMap.sum_apply, Finsupp.single_apply]
  have hbil : ∀ (β : LinearMap.BilinForm ℤ X) (c d : Fin r → ℤ),
      β (∑ i, c i • b i) (∑ j, d j • b j) = ∑ i, ∑ j, c i * d j * β (b i) (b j) := by
    intro β c d
    simp [map_sum, map_smul, LinearMap.sum_apply, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    rw [Finset.sum_comm]
  let L : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun i j => lam (C i j) + lam (C j i)
  have hlam : ∀ β : LinearMap.BilinForm ℤ X, (∀ x y, β x y = β y x) →
      2 * lam β = ∑ i, ∑ j, L i j * β (b i) (b j) := by
    intro β hβ
    have h1 : lam β = ∑ i, ∑ j, β (b i) (b j) * lam (C i j) := by
      conv_lhs => rw [hexp β]
      simp [map_sum, map_smul]
    have h2 : lam β = ∑ i, ∑ j, β (b i) (b j) * lam (C j i) := by
      rw [h1, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hβ]
    calc 2 * lam β = lam β + lam β := by ring
      _ = _ := by
        nth_rewrite 1 [h1]
        rw [h2]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [L, Matrix.of_apply]; ring
  have hs : Lᵀ = L := by
    ext i j; simp [L, add_comm]
  have hp : ∀ v : Fin r → ℤ, v ≠ 0 → 0 < v ⬝ᵥ L *ᵥ v := by
    intro v hv
    let l : X →ₗ[ℤ] ℤ := ∑ i, v i • b.coord i
    have hl : ∀ k, l (b k) = v k := by
      intro k; simp [l, Finsupp.single_apply]
    have hl0 : l ≠ 0 := by
      intro h; apply hv; funext k; rw [← hl k, h]; rfl
    have hsq : ∀ x y, GlobalTheory.PolFan.sqForm l x y = l x * l y := by
      intro x y; simp [GlobalTheory.PolFan.sqForm]
    have hsym : ∀ x y, GlobalTheory.PolFan.sqForm l x y = GlobalTheory.PolFan.sqForm l y x := by
      intro x y; rw [hsq, hsq, mul_comm]
    have h2 := hlam _ hsym
    have h3 : v ⬝ᵥ L *ᵥ v = 2 * lam (GlobalTheory.PolFan.sqForm l) := by
      rw [h2]
      simp only [hsq, hl, dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [h3]; have := hpos l hl0; omega
  have hPD := posDef_of_pos_int L hs hp
  obtain ⟨D, m, a', hD, hspan, hsum⟩ := GlobalTheory.Poinc.SumSq.exists_smul_eq_sum_vecMulVec_span r L hPD
  have hentry : ∀ i j, (D : ℤ) * L i j = ∑ k, a' k i * a' k j := by
    intro i j
    have := congrFun (congrFun hsum i) j
    simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
  refine ⟨2 * D, m, fun k => ∑ i, a' k i • b i, by omega, ?_, ?_⟩
  · have hfun : (fun k => ∑ i, a' k i • b i) = ⇑b.equivFun.symm.toLinearMap ∘ a' := by
      funext k; simp [Module.Basis.equivFun_symm_apply]
    rw [hfun, Set.range_comp, Submodule.span_image, hspan, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr b.equivFun.symm.surjective
  · intro β hβ
    simp only [hbil]
    rw [Finset.sum_comm]
    have : ∀ i, (∑ y, ∑ x, a' y i * a' y x * β (b i) (b x)) = ∑ j, (D : ℤ) * L i j * β (b i) (b j) := by
      intro i
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hentry, Finset.sum_mul]
    simp only [this]
    have h2 := hlam β hβ
    push_cast
    rw [mul_comm 2 (D : ℤ), mul_assoc, h2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.Poinc.SumSqFunctional
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePointFieldStatement
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fibre_point_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ), p.Prime → (p : ℂ) ∈ W.nonunits → (p : c'.F) ∈ (c'.V W).nonunits → ∀ (A : Type) [CommRing A] [IsDomain A] (ξ : Sp A ⟶ Y.X), ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Set.range Y.j → ∀ (K : Type) [Field K] (ψ : A →+* K), Function.Injective ψ → ∃ yy : Sp K ⟶ Xo'.XF c', yy ≫ Y.j = spMap ψ ≫ ξ := by
  first | exact @GlobalTheory.FlatModel.GenPt.exists_lift_genericFibre | exact GlobalTheory.FlatModel.GenPt.exists_lift_genericFibre | (intros; apply GlobalTheory.FlatModel.GenPt.exists_lift_genericFibre <;> assumption)
end

