import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0374
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0281
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0302
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0333
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0298
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0280
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0336
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0365
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0376
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0334
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0372
import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0702
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0344
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0338
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0350
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0375
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0377
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0458
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsStagesClauses
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import ReciprocityTheory.Hypotheses.GalCoh
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0032
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicChainDatumCharacterLawsJointKernel
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU
open scoped TensorProduct

namespace GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pt

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  {A : AdData t u μ St} {a : 𝓞 D.host.E}

theorem xiAd_eq_of_isPtAd (hW : ∀ i hi, PtAway A a i hi) {i : ℕ} {hi : i + 1 ≤ D.R.m}
    {β : (St i (Nat.le_of_succ_le hi)).Ch} {β' : (St (i + 1) hi).Ch} {x : UA D i (Nat.le_of_succ_le hi)} {x' : UA D (i + 1) hi}
    {p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i} {p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (i + 1)}
    (hp : IsPtAd A a i (Nat.le_of_succ_le hi) β x p) (hp' : IsPtAd A a (i + 1) hi β' x' p') (z : HomE D.host.E (D.R.N i) (D.R.N (i + 1))) :
    xiAd A a i hi β β' x x' z = t.seam.σ₀ (xiPt A i hi β β' p p' (seamHom t.seam (inFr
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
      (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))) := by
  have h : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x' p' := ⟨⟨p, hp⟩, ⟨p', hp'⟩⟩
  dsimp only [xiAd]
  rw [dif_pos h, hW i hi β β' x x' x x' p p' _ _ hp hp' h.1.choose_spec h.2.choose_spec (fun _ _ => ⟨rfl, rfl⟩)]

theorem exists_u1Af_det (k : ℕ) (hk : k ≤ D.R.m) {g : GL (Fin (D.R.N k)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    (hg : g ∈ UPts (sigD D) (gramN D k hk) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = Matrix.GeneralLinearGroup.det g := by
  have hU := det_in_unitary_one D.host.F D.host.E (sigD D) _ (gramN D k hk) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D k hk) g hg
  set x := Matrix.GeneralLinearGroup.det g with hx
  have hx1 : x * conjId (sigD D) x = 1 := hU
  have h2 : (x : D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) * sigR (sigD D) _ (x : _) = 1 := congrArg Units.val hx1
  refine ⟨⟨Units.map (Matrix.scalar (Fin 1) : _ →+* Matrix (Fin 1) (Fin 1) _).toMonoidHom x, ?_⟩, ?_⟩
  · change cT (sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (Matrix.scalar (Fin 1) (x : D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * (1 : Matrix (Fin 1) (Fin 1) D.host.E).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) * Matrix.scalar (Fin 1) (x : D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) = (1 : Matrix (Fin 1) (Fin 1) D.host.E).map (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    simp only [cT, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1; funext _; rw [mul_comm]; exact h2
  · apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]

end Pt

theorem adLawAt_xiAd : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => AdLawAt A dtU a (xiAd A a) (muOf t u μ dtU)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie
  have hPt : PtEx A a ∧ ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c) := GlobalTheory.T.chartPoints_exist_and_classPoints_representatives A dtU a hPin hTie
  have hE := hPt.1
  have hCo : ∀ c, cosetOf A (t.m2 + 1) (cpl_lt t μ).le ((St _ (cpl_lt t μ).le).chOf c) (A.pt _ (cpl_lt t μ).le c) = A.yb c :=
    GlobalTheory.T.couplingCoset_eq_chartPointCoset A dtU a hPin hTie
  have hMu : MuLaw t u μ dtU := GlobalTheory.T.stepCharacterLaws_normOneIdeles_of_kernelChain A dtU a hPin hTie
  have hm := m_eq t μ
  have hW : ∀ i hi, PtAway A a i hi := by
    intro i hi
    rcases lt_trichotomy i t.m2 with h | h | h
    · exact GlobalTheory.T.finiteDatum_dependsOnlyAtBadPlaces_matrixStep A dtU a hPin hTie i hi h
    · exact GlobalTheory.T.finiteDatum_dependsOnlyAtBadPlaces_firstCoupledStep A dtU a hPin hTie i hi h
    · exact GlobalTheory.TwV.AwayTop.ptAway_top A dtU a hPin hTie i hi (by omega)
  have hLev : ∀ i hi, LevAt A dtU a i hi := by
    intro i hi
    rcases lt_trichotomy i t.m2 with h | h | h
    · exact GlobalTheory.T.finiteDatum_levelEquivariance_at_matrixSteps A dtU a hPin hTie hE hMu i hi h (hW i hi)
    · exact GlobalTheory.T.adelicDatum_level_equivariance_first_coupled_step A dtU a hPin hTie hE hMu i hi h (hW i hi)
    · exact GlobalTheory.T.lastStep_adelicDatum_level_equivariance A dtU a hPin hTie hE hMu i hi (by omega) (hW i hi)
  have hRat : RatLaw A a := GlobalTheory.T.finiteAdelicDatum_rationalInvariance_of_kernelChain A dtU a hPin hTie hE hW
  have hSize : SizeLaw A a := GlobalTheory.T.adelicDatum_invariance_support_kernelChain A dtU a hPin hTie hE
  have hInt : ∀ i hi β β' x x' z, IntOff (t.O u μ).S (xiAd A a i hi β β' x x' z) := GlobalTheory.T.adelicFiniteDatum_integralOffBadPrimes A dtU a hPin hTie hE
  refine
    { read := ?_
      rat := hRat
      lev := fun i hi => hLev i hi
      away := ?_
      loc := fun i hi β β' x x' => (hSize i hi β β' x x').1
      supp := fun i hi β β' x x' => (hSize i hi β β' x x').2
      int := hInt
      mu_read := fun i hi => (hMu i hi).1
      mu_cls := ?_
      mu_mul := fun i hi => (hMu i hi).2.1
      mu_alg := fun i hi => (hMu i hi).2.2.1
      mu_unr := fun i hi => (hMu i hi).2.2.2.1
      mu_rat := fun i hi => (hMu i hi).2.2.2.2 }
  · intro i hi c c' z
    rw [xiAd_eq_of_isPtAd hW (hPt.2 i _ c) (hPt.2 (i + 1) hi c')]
    rcases lt_trichotomy i t.m2 with h | h | h
    · rw [hTie.chain.2.2.1 i h c c', xiPt, dif_pos h]
    · subst h
      rw [hTie.chain.2.2.2.1 c c', xiPt, dif_neg (lt_irrefl _), if_pos rfl, hCo c']
    · obtain rfl : i = t.m2 + 1 := by omega
      rw [hTie.chain.2.2.2.2.1.2 c c', xiPt, dif_neg (by omega), if_neg (by omega), hCo c]
  · intro i hi β β' x x' x₁ x₁' hx
    funext z
    obtain ⟨p, hp⟩ := hE i _ β x
    obtain ⟨p', hp'⟩ := hE (i + 1) hi β' x'
    obtain ⟨p₁, hp₁⟩ := hE i _ β x₁
    obtain ⟨p₁', hp₁'⟩ := hE (i + 1) hi β' x₁'
    rw [xiAd_eq_of_isPtAd hW hp₁ hp₁', xiAd_eq_of_isPtAd hW hp hp', hW i hi β β' x x' x₁ x₁' p p' p₁ p₁' hp hp' hp₁ hp₁' hx]
  · intro i hi k hk c
    obtain ⟨y, hy⟩ := exists_u1Af_det k hk ((St k hk).y c).2
    rw [← hy, (hMu i hi).1 y, hTie.dt k hk c y hy]

end GlobalTheory.TwV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.Adm8AndLambdaUsed
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.NRows.OverX

set_option maxHeartbeats 2000000 in

theorem parts_lam : PrN → GlobalTheory.NRows.HypothesesX → OverRows fun _ _ _ _ w Z _ _ z p0 Y => ReadL z.R z.F p0 Y →
    (∃ L : SizeData₂ (w.st Z).toD7, Nonempty (ParameterChoice' (w.st Z).toD7 L)) → SumRepresentations.adm8 (w.st Z).toD7 ∧ GlobalTheory.NRows.LamUsed (w.st Z).toD7 := by
  intro hN hPX
  refine EvG.imp (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev) fun K _ _ _ _ hHost => ?_
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, ?_⟩
  intro B f T hO _ _ _ _ w _ Z Wt hX z p0 Y hHo hEx _ hGrp _ hRd hp
  have hH : Formalism.IndefR.Links.HostHyp (w.st Z).toD7 := (hHost (w.st Z) hO).1
  have hGS : Formalism.L2.DIV.GoodStable z.Xg := by
    have hI := GlobalTheory.DimPartsCompare.TameTie.idemTie hN.greenC
      (GlobalTheory.DimPartsCompare.tameTie_of_typesTrue (D := (w.st Z).toD7) hGrp).2.1
    refine GlobalTheory.Mem.R3.GoodDual.goodStable_of_coeff (w.st Z).B.embLL z.Xg z.good.irr fun g => ?_
    apply (w.st Z).B.embLL.injective
    rw [z.good.2, z.good.2, map_inv, GlobalTheory.Mem.R3.GoodDual.goodIdempotent_coeff_inv_eq_coeff hI]
  have hT : TypesTrue (w.st Z).toD7.ntypes z.R.C.P z.R.C.W := by
    rw [z.lev.C, w.C_eq]
    exact hGrp
  have hME := GlobalTheory.T.multiplicity_equality_statement hPX.ana hPX.dsc hN.decay hN.hc hPX.trc hPX.dm hPX.flath hPX.pc hPX.hcc hPX.lc hPX.lw hN.zel
    hN.what₂.geo hN.greenC z.R z.F hHo.ok z.pins.char hEx hH hp B.ccK_top z.pins.keep.guard
    (GlobalTheory.LiftRows.Inh.goodTypes_of_typesTrue z.pins.char.base.lev hT)
  have hIR : Formalism.BasicNotions.Rows.IsotRank (w.st Z).toD7.what₂ :=
    GlobalTheory.Mem.R3.isotRank_of_multEq hPX.weil hPX.ds hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG _ Y z.pins hHo hH hGS
      (GlobalTheory.CuspDec.cuspDecomp hN.hc hN.decay _) hME
  exact ⟨GlobalTheory.T.thetaLift_forms_internal_direct_sum_isotypic hPX.weil hPX.ds hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y hRd z.pins hHo hH hIR,
    GlobalTheory.T.downLift_upLift_positiveScalar_usedTuples hPX.weil hPX.ds hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y hRd z.pins hHo hH⟩

end GlobalTheory.NRows.OverX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetTwistedFrameOperatorIdentityDenominator
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem det_zT_ne_zero {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)
    {n : ℕ} (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (hf : ∀ τ, (f τ).det ≠ 0) (τ : D.what₂.Tau) :
    (zT X D pos f τ).det ≠ 0 := by
  unfold zT
  split_ifs
  · have hu : IsUnit (f τ).det := isUnit_iff_ne_zero.mpr (hf τ)
    have e : ((f τ)⁻¹).transpose.submatrix id Fin.rev = ((f τ)⁻¹).transpose.submatrix id (Fin.revPerm : Equiv.Perm (Fin n)) := rfl
    rw [e, Matrix.det_permute', Matrix.det_transpose]
    refine mul_ne_zero (by simp [Units.ne_zero]) ?_
    intro h0
    have := Matrix.det_nonsing_inv_mul_det (f τ) hu
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  · exact hf τ

theorem opId_denom : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → subD X Kc j G * numD X Kc j = denD X Kc j * (cD X Kc j (ι (cOp X D pos j s)) * trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) := by
  intro p _ X D pos Kc _ _ ι j hN ν hν Q hQ Gc G hR hG s hs
  apply sub_eq_zero.mp
  apply GlobalTheory.T.symbolFramePolynomial_eq_zero_of_generic_vanish X D pos Kc ι j hN
  intro d f' hf hdf
  have hZ : ι (∏ τ, (zT X D pos f' τ).det ^ eT X D pos (j + 1) τ) ≠ 0 := by
    rw [map_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (det_zT_ne_zero X D pos f' hf τ)
  have hL := GlobalTheory.T.operatorIdentity_leftSide_complexPoint X D pos Kc ι j hN ν hν Q hQ Gc G hR hG d f' hf hdf
  have hRr := GlobalTheory.T.transportedPolynomial_complexPoint_evaluation X D pos Kc ι j hN ν hν Q hQ s hs d f' hf
  have hc : evD X D pos ι hN d f' (cD X Kc j (ι (cOp X D pos j s))) = ι (cOp X D pos j s) := by
    simp [evD, cD]
  have hS : (∏ τ, s τ ^ (-(szT X D pos j τ))) * ∏ τ, s τ ^ szT X D pos j τ = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun τ _ => by rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (hs τ))]
  rw [map_sub, sub_eq_zero]
  apply mul_right_cancel₀ hZ
  rw [hL, (evD X D pos ι hN d f').map_mul (denD X Kc j), (evD X D pos ι hN d f').map_mul (cD X Kc j _), hc, mul_assoc ((evD X D pos ι hN d f') (denD X Kc j)), mul_assoc (ι (cOp X D pos j s)), hRr, ← ι.map_mul]
  congr 2
  unfold cOp
  linear_combination (-(sgO X D pos j * (∏ τ, (f' τ).det ^ (-(wT X D pos j τ))) * GL3Theta.evFr D Q (dfr X D hN d f'))) * hS

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvParamsOfRows
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.Mem.RowsLed

open Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB in
set_option maxHeartbeats 1000000 in

theorem ev_exists_sizeData_untwisted : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → X.V.div.etaF = 6 * K.s.x ^ (-K.C.P.CF) →
    (∀ w, X.toD7.what₂.muAt w = X.toD7.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ X.toD7.R.m → X.toD7.what₂.Aj j w = 0) →
    ∃ L : SizeData₂ X.toD7, L.sc = K.s ∧ Nonempty (ParameterChoice' X.toD7 L) := by
  refine ⟨1, one_pos, fun eps C8 h0 _ h1 _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C hC _ _ => ?_⟩⟩
  obtain ⟨c1, hN⟩ := szRow_numAt eps h0 h1 C hC
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  obtain ⟨c2, hN⟩ := hN cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  obtain ⟨x1, hN⟩ := hN ch ((le_max_left _ _).trans hch)
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC ((le_max_right _ _).trans hcD) ((le_max_right _ _).trans hch)
  refine ⟨max x0 x1, ?_⟩
  rintro K rfl rfl rfl hs hx X hO heta hA
  have hP := K.ok
  obtain ⟨sp, hT, hY, hA', hV, hz, hB, -⟩ := hO
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  have hlev : ∀ p ∈ K.Lv.host.levelPrimes, K.Lv.host.cls p = .splitK := (Pre.ofCh K.P K.Lv sp hT hY hA' hV hz).level_split
  have hdel : D.s.Del = (Delv K.s K.cD : ℚ) := by
    have τ : Tau K.P.R := tauPl D (false, 0)
    have hk := K.P.R.m_add_three_le_k
    have hm := K.P.R.two_le_m
    have hl : 0 + 1 < K.P.R.k - 1 := by omega
    have a1 := D.s.cloud_gap K.P.u₀ τ 0 hl
    have a2 := congrArg₂ (· - ·) ((hP.hc K.P.u₀).1 τ ⟨0, by omega⟩) ((hP.hc K.P.u₀).1 τ ⟨0 + 1, hl⟩)
    have a3 := a1.symm.trans a2
    have e : K.P.R.k - 2 - 0 = K.P.R.k - 2 - (0 + 1) + 1 := by omega
    dsimp only at a3
    rw [e] at a3
    push_cast at a3
    linarith
  obtain ⟨L, e1, -, -, e4⟩ := hx0 K.s D (fun t => K.a t.1) (fun t => K.b t.1) hs ((le_max_left _ _).trans hx) hP.rank hP.val
    (hP.hc K.P.u₀) hP.dlog hdel hP.ct2 hP.card heta (fun u => by
      have e : (D.mem u).A.GamP = K.Lv.GamP := Cc.A_GamP u
      rw [e, K.Gam_eq, GamS, Real.log_exp]; rfl)
    (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top K.P.u₀ τ t h ht) hA
  obtain ⟨⟨M⟩, -, -⟩ := hN D L (by rw [e1]; exact hs) (by rw [e1]; exact (le_max_right _ _).trans hx) e4
    ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩
  exact ⟨L, e1, ⟨M.params⟩⟩

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}

theorem aj_untw {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} (t : RowsT K w Z Wt p0) :
    ∀ v, (w.D Z).what₂.muAt v = (w.D Z).what₂.mu0 → ∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → (w.D Z).what₂.Aj j v = 0 := by
  intro v hv j h1 h2
  have hn : v ∉ Wt := fun h => (V4.Model.mem_iff t.mu v).1 h hv
  have hc : (w.D Z).what₂.places.conj v ∉ Wt := fun h =>
    (V4.Model.mem_iff t.mu _).1 h (((w.st Z).W.muAt_conj v).trans hv)
  have a := t.untw v hn j h1 h2
  have b := t.untw _ hc j h1 h2
  unfold Rows.Data.Aj
  rw [hv, a.1, a.2, b.1]
  rfl

theorem ev_exists_sizeData_of_rows : GlobalTheory.Mem.Top.Ev fun K => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)), RowsT K w Z Wt p0 → K.Over B.toPre → ∃ L : SizeData₂ (w.D Z), L.sc = K.s ∧ Nonempty (ParameterChoice' (w.D Z) L) :=
  V4.Model.ev_imp ev_exists_sizeData_untwisted fun _ H _ _ _ w Z _ _ t hO => H (w.st Z) hO t.etaF (aj_untw t)

end GlobalTheory.Mem.RowsLed

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaInvariantUnderUnramifiedTwistOfWeilDelign
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.IneUnrTwist

open Formalism.MainNotions Formalism.ConjugateSelfDual GlobalTheory.WeilDeligne ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct

theorem wd_inePol_twist {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w} (a χ : WD h) (h1 : χ.lpDim = 1)
    (hu : χ.unr) {s : G E Ω} (hs : s ∈ Ine (F := E) B) : (a.lpChar χ).inePol s = a.inePol s := by
  induction a using WD.ind with | hP n a => ?_
  induction χ using WD.ind with | hP m c => ?_
  rw [WD.lpDim_mk] at h1
  rw [WD.unr_mk] at hu
  rw [WD.lpChar_mk, WD.inePol_of_mem_Ine _ hs, WD.inePol_of_mem_Ine _ hs, WD.charPol_mk, WD.charPol_mk,
    WDRep.tensor_ρ, hu.2]
  let e : (Fin m → ℂ) ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq _ _ (by simpa using h1)
  let E' := (TensorProduct.congr (LinearEquiv.refl ℂ (Fin n → ℂ)) e).trans (TensorProduct.rid ℂ _)
  rw [← LinearEquiv.charpoly_conj E']
  congr 1
  refine LinearMap.ext fun v => ?_
  simp [E', LinearEquiv.conj_apply]

theorem main : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → IneUnr D := fun D T w a χ h1 hu s hs => by
  rw [T.inePol w _ s hs, T.inePol w _ s hs, T.char w a χ h1]
  exact wd_inePol_twist _ _ ((T.dim w χ).trans h1) ((T.unr w χ).1 hu) hs

end GlobalTheory.IneUnrTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfinitesimalWeightOfDualStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinitesimal_weight_of_dual : ∀ (D : D7) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), HeckeOpen D M tup → ∀ (i : D.nd.Loc) (a : Formalism.L2.NG.AlgWt D.host.E D.R.nV) (τ : D.host.E →+* ℂ) (lam : Fin D.R.nV → ℤ), (M.loc i).wt.IsDual a → a.HWAt τ lam → D.naut.infWt i τ = Formalism.L2.NG.infOf lam := by
  first | exact @GlobalTheory.LocInfWt.infWt_eq_infOf | exact GlobalTheory.LocInfWt.infWt_eq_infOf | (intros; apply GlobalTheory.LocInfWt.infWt_eq_infOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfinityTypeEtaTildeAtCmTypeEmbeddingsEqHalfStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinityType_etaTilde_at_cmTypeEmbeddings_eq_half : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C), NCharTied D cf C tp → ∀ t, D.naut.infG D.naut.etaT (Formalism.L2.embT D t) = {(1 / 2 : ℂ)} := by
  first | exact @GlobalTheory.EtaInfType.main | exact GlobalTheory.EtaInfType.main | (intros; apply GlobalTheory.EtaInfType.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteArithmeticGroupMoveStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_arithmeticGroup_move : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → S.Pair → S.Move) := by
  first | exact @GlobalTheory.TwV.Xc.site_move | exact GlobalTheory.TwV.Xc.site_move | (intros; apply GlobalTheory.TwV.Xc.site_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteContractionIdentityOperatorHalfStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_contractionIdentity_operatorHalf : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ (d : Dec J std), ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (Φ₀ : ∀ j, MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w]) (τ : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w] →ₗ[ℂ_[D.what₂.places.resChar w]] XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w]) (sc : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → ℂ_[D.what₂.places.resChar w]) (sO : ∀ j, (sysS H X std).Lt j → ℂ_[D.what₂.places.resChar w]) (Gm : ∀ j, (sysS H X std).Lt j → ((ex.tw.fm u μ).lat j).V → ((sysS H X std).Pj j).Xsp), ∀ j < D.R.m, ∀ (cK : ℂ_[D.what₂.places.resChar w]) (hN : RankTie (sysS H X std) D j), MoveH S.Y u μ (kaAt X H hT).cmp (fun j La => glInv (sysS H X std) j (BOf d.fd2 j La)) Gm j → TieOpS (Y := S.Y) t u μ (clsAt X H) Gm sO j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) (ι := ι) (Φ₀ j) → KernelEntryDegreeCondition (Y := S.Y) t u μ (clsAt X H) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) → DelYEqH S.Y (fun j La' => VOf ℂ_[D.what₂.places.resChar w] d.fd2 (ltC S.g S.hLT) j La') τ j → (∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → cK * (Formalism.L2.G.Pend.cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO j La) * ι (d.uS S j La) * ι (d.uT S j La') = sc j La'.1 La'.2) → DelPolAt (Y := S.Y) t u μ (clsAt X H) (kaAt X H hT).cmp (fun j => clsAt X H (j + 1)) (phiH D Φ₀ τ sc) (srOf S.Y) j cK) := by
  first | exact @GlobalTheory.TwV.DelB.delPolAt_site | exact GlobalTheory.TwV.DelB.delPolAt_site | (intros; apply GlobalTheory.TwV.DelB.delPolAt_site <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteLatticeTuplePairsAdmissibleStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_latticeTuplePairs_admissible : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair) := by
  first | exact @GlobalTheory.pairOK_allSites | exact GlobalTheory.pairOK_allSites | (intros; apply GlobalTheory.pairOK_allSites <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteScalarsAgreeAwayFromPlaceStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_scalars_agree_awayFromPlace : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pair → ∀ v π, IsUnifAt J v π → ∀ j < D.R.m, ∀ a b : (sysS H X std).G.Kf, S.E.iK a = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (-((sysS H X std).vm v (j + 1))) * TaylorLogMetric.lamC S.lam (S.muT (j + 1) π * chiI J π ^ (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) → S.E.iK b = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ ((sysS H X std).vm v (j + 1)) * TaylorLogMetric.lamC S.lam ((S.muT (j + 1) π)⁻¹ * chiI J π ^ (-((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ)))) → ∀ (La Lb : (sysS H X std).Lt j) (La' Lb' : (sysS H X std).Lt (j + 1)), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → SameAway (hT := hT) (H := H) (X := X) std v (j + 1) La' Lb' → GlobalTheory.TwU.pPow (sysS H X std) j La La' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j La La') * S.E.iK (a ^ len (sysS H X std) v j Lb.2 * b ^ len (sysS H X std) v (j + 1) Lb'.2) = GlobalTheory.TwU.pPow (sysS H X std) j Lb Lb' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j Lb Lb') * S.E.iK (a ^ len (sysS H X std) v j La.2 * b ^ len (sysS H X std) v (j + 1) La'.2)) := by
  first | exact @GlobalTheory.TwV.Xc.AwayId.scal_away | exact GlobalTheory.TwV.Xc.AwayId.scal_away | (intros; apply GlobalTheory.TwV.Xc.AwayId.scal_away <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SourceScalarLatticeTupleConstantStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sourceScalar_latticeTuple_constant : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j < D.R.m), Nonempty (Lv.comp (j + 1)) → ∀ La : (sysS H X std).Lt j, dPow (mM d j hj.le La).1 (fun τ => -(wT (sysS H X std) D (hT.gat_pos u w hg) j τ)) * sPt d j hj.le La * d.uS S j La = kS J j hj.le La.1) := by
  first | exact @GlobalTheory.TwV.DelA.source_scalar_const | exact GlobalTheory.TwV.DelA.source_scalar_const | (intros; apply GlobalTheory.TwV.DelA.source_scalar_const <;> assumption)
end

