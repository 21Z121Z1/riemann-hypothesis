import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0378
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0349
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0032
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0273
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0270
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0276
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0145
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0363
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0369
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0360
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0375
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0370
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0379
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0374
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0362
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0356
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import ReciprocityTheory.Hypotheses.GalCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0751

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicChainDatumCharacterLawsJointKernelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicChainDatum_characterLaws_jointKernel : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => AdLawAt A dtU a (xiAd A a) (muOf t u μ dtU)) := by
  first | exact @GlobalTheory.TwV.adLawAt_xiAd | exact GlobalTheory.TwV.adLawAt_xiAd | (intros; apply GlobalTheory.TwV.adLawAt_xiAd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.Adm8AndLambdaUsedStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adm8_and_lamUsed_of_parameterChoice : PrN → GlobalTheory.NRows.HypothesesX → OverRows fun _ _ _ _ w Z _ _ z p0 Y => ReadL z.R z.F p0 Y → (∃ L : SizeData₂ (w.st Z).toD7, Nonempty (ParameterChoice' (w.st Z).toD7 L)) → SumRepresentations.adm8 (w.st Z).toD7 ∧ GlobalTheory.NRows.LamUsed (w.st Z).toD7 := by
  first | exact @GlobalTheory.NRows.OverX.parts_lam | exact GlobalTheory.NRows.OverX.parts_lam | (intros; apply GlobalTheory.NRows.OverX.parts_lam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetTwistedFrameOperatorIdentityDenominatorStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detTwistedFrame_operatorIdentity_denominator : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → ∀ (s : D.what₂.Tau → ℂ), (∀ τ, s τ ≠ 0) → subD X Kc j G * numD X Kc j = denD X Kc j * (cD X Kc j (ι (cOp X D pos j s)) * trDY X Kc j D (eIdx X D pos j hN) (phi0 X D pos ι j) (polDY D s Q (N' := D.R.N (j + 1)))) := by
  first | exact @GlobalTheory.TwV.DelA.opId_denom | exact GlobalTheory.TwV.DelA.opId_denom | (intros; apply GlobalTheory.TwV.DelA.opId_denom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaInvariantUnderUnramifiedTwistOfWeilDelignStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaInvariantUnderUnramifiedTwist_of_weilDeligne : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → IneUnr D := by
  first | exact @GlobalTheory.IneUnrTwist.main | exact GlobalTheory.IneUnrTwist.main | (intros; apply GlobalTheory.IneUnrTwist.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteArithmeticGroupMovesFrames
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section
namespace GlobalTheory.TwV

theorem move_at_site : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Move) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD
  exact GlobalTheory.T.kernelSite_arithmeticGroup_move S hD ⟨J.alg0, J.alg⟩ (pos_at_site S) (GlobalTheory.T.kernelSite_latticeTuplePairs_admissible S hD)

end GlobalTheory.TwV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteAwayOfPositivePair
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc.AwayInd

set_option maxHeartbeats 4000000 in

theorem away_of_pos_pair : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    KIn t → S.Pos → S.Pair → S.Away) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hSpl hK hPos hPair
  intro v j hj
  have hgood := J.one.good
  have hint := J.one.int
  have hp : (D.what₂.places.resChar w).Prime := Fact.out
  obtain ⟨hcop, hSS, -, -⟩ := GlobalTheory.T.level_badPrimes_coprime_residueChar S hDict hSpl
  obtain ⟨P, hPof, happ, hpP, hpP2⟩ := GlobalTheory.T.exists_prime_under_firstFactor_at_placeOverP _ _ _ _ _ (A0 J) hint hSpl.1 v
  obtain ⟨a, b, hab, ha, hb⟩ := GlobalTheory.XcSplit.prime_not_stable _ _ (sigD D) _ _ _ (A0 J) _ hgood hint hSpl.1 v P hPof
  have hpC : (((D.what₂.places.resChar w : ℕ)) : 𝓞 D.host.E) ∈ (Formalism.L2.Col.conjPrime₂ P).asIdeal := by
    rw [Formalism.L2.Col.mem_conjP, map_natCast]; exact hpP
  have hcopE : IsCoprime (((t.rd u μ).lev : ℕ) : 𝓞 D.host.E) ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.E) := by
    have h := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (𝓞 D.host.E))
    simpa using h
  have hlev : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal →
      (((t.rd u μ).lev : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal := by
    intro Q hpQ hlQ
    obtain ⟨x, y, hxy⟩ := hcopE
    have h1 : (1 : 𝓞 D.host.E) ∈ Q.asIdeal := hxy ▸ Q.asIdeal.add_mem (Q.asIdeal.mul_mem_left x hlQ) (Q.asIdeal.mul_mem_left y hpQ)
    exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have hab' : (b : D.host.E) = D.host.conj (a : D.host.E) := by
    rw [hab]
    first | exact Formalism.L2.PairingIndexBounds.F.sig_conj D _ | exact Formalism.L2.Fam.sig_eq_conj D.host D.sp.cm _ | exact Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D _
  refine ⟨P, ⟨a, b, hab', ha, hb⟩, GlobalTheory.T.localisation_inverseHalfDifferent_eq_one_unramified D _ hp P hpP hpP2, fun h => hSS P h hpP, fun h => hSS _ h hpC,
    hlev P hpP, hlev _ hpC, hPof, happ, ?_⟩
  by_cases hc : Nonempty ((sysS H X std).Lv.comp j) ∧ Nonempty ((sysS H X std).Lv.comp (j + 1))
  · obtain ⟨⟨c⟩, ⟨c'⟩⟩ := hc
    obtain ⟨π, hπU, hoff, hord⟩ := GlobalTheory.T.exists_normOne_idele_order_one_trivial_elsewhere _ _ (sigD D) _ _ _ (A0 J) _ hgood v
    have hU : IsUnifAt J v π := ⟨hπU, hoff, hord⟩
    obtain ⟨x, y, hx0, hy0, hx, hy⟩ := GlobalTheory.T.two_units_at_place_uniformizing_idele S hDict hSpl hK hPos v π hU j hj c c'
    refine ⟨x, y, hx0, hy0, ?_⟩
    intro La Lb La' Lb' h1 h2 h3 h4 haw
    have e1 : La.1 = Lb.1 := congrArg (fun z : (sysS H X std).Lt j × (sysS H X std).Lt (j + 1) => z.1.1) haw
    have e2 : Function.update La.2 ((sysS H X std).vJ j v) ⊥ = Function.update Lb.2 ((sysS H X std).vJ j v) ⊥ :=
      congrArg (fun z : (sysS H X std).Lt j × (sysS H X std).Lt (j + 1) => z.1.2) haw
    have e3 : La'.1 = Lb'.1 := congrArg (fun z : (sysS H X std).Lt j × (sysS H X std).Lt (j + 1) => z.2.1) haw
    have e4 : Function.update La'.2 ((sysS H X std).vJ (j + 1) v) ⊥ = Function.update Lb'.2 ((sysS H X std).vJ (j + 1) v) ⊥ :=
      congrArg (fun z : (sysS H X std).Lt j × (sysS H X std).Lt (j + 1) => z.2.2) haw
    have hA : SameAway (hT := hT) (H := H) (X := X) std v j La Lb := ⟨h1, h3, e1, e2⟩
    have hA' : SameAway (hT := hT) (H := H) (X := X) std v (j + 1) La' Lb' := ⟨h2, h4, e3, e4⟩
    refine ⟨GlobalTheory.T.eqOffPrime_kernelLattices_of_agreeAway S hDict hSpl v P hPof j hj.le La Lb hA, GlobalTheory.T.eqOffPrime_kernelLattices_of_agreeAway S hDict hSpl v P hPof (j + 1) hj La' Lb' hA', ?_, ?_,
      GlobalTheory.T.movedDatum_eq_of_latticeTuples_agreeAway S hDict hSpl v j hj La Lb La' Lb' hA hA', GlobalTheory.T.kernelSite_scalars_agree_awayFromPlace S hDict hSpl hPair v π hU j hj x y hx hy La Lb La' Lb' hA hA'⟩
    · have hLb : Lb = (La.1, Lb.2) := Prod.ext e1.symm rfl
      rw [hLb]
      exact GlobalTheory.T.latticeTuple_frameMatrices_eq_of_same_component S hDict hSpl j La.1 La.2 Lb.2
    · have hLb : Lb' = (La'.1, Lb'.2) := Prod.ext e3.symm rfl
      rw [hLb]
      exact GlobalTheory.T.latticeTuple_frameMatrices_eq_of_same_component S hDict hSpl (j + 1) La'.1 La'.2 Lb'.2
  · have h1 : (sysS H X std).vEqK 1 0 := GlobalTheory.UnitK.vEqK_zero_of_norm_one _ _ S.E.toCEmb 1 (by simp)
    refine ⟨1, 1, h1, h1, ?_⟩
    intro La Lb La' Lb'
    exact absurd ⟨⟨La.1⟩, ⟨La'.1⟩⟩ hc

end GlobalTheory.TwV.Xc.AwayInd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteSeriesScalarPowIntegral
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

noncomputable section
namespace GlobalTheory.TwV

theorem scal_at_site : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Scal) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hd
  exact GlobalTheory.T.thetaSeries_scalar_bounded_of_pos_pair S hd ⟨J.alg0, J.alg⟩ (pos_at_site S) (GlobalTheory.T.kernelSite_latticeTuplePairs_admissible S hd)

end GlobalTheory.TwV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalCompatibilityOfClassMapsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_compatibility_of_class_maps : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : GlobalTheory.NPin.Pin hL D) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), IsRc hL P.T I rc → (∀ k v, IsClassMap D.naut.lpDim (rc k v)) → GlobalTheory.HeightCounting.Up.CenLoc D P.M → LocComp D rc := by
  first | exact @GlobalTheory.LocCompTy.main | exact GlobalTheory.LocCompTy.main | (intros; apply GlobalTheory.LocCompTy.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TargetFrameMapEqComplexBlockActionScalarStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.targetFrameMap_eq_complexBlockAction_scalar : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (c : Kc), c ≠ 0 → ∀ (j : ℕ) (hN : RankTie X D j) (La' : X.Lt (j + 1)) (M : GL (Fin (D.R.N (j + 1))) D.host.E), StdU D M → FrIs fd ρ (j + 1) La' (rkT X D hN) M → ∀ (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ P : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ, P ∈ WtPol ℂ (extNu (D.R.N (j + 1)) ν) → GlobalTheory.FrameB.tauV Kc fd c j La' (phi0 X D pos ι j P) = (c ^ (∑ τ, szT X D pos j τ) * ι (∏ τ, embT D τ M.1.det ^ wT X D pos j τ)) • MvPolynomial.map ι (actC X D pos (j + 1) (rkT X D hN) M⁻¹ (phiC X D pos (j + 1) (rkT X D hN) (wT X D pos j) P)) := by
  first | exact @GlobalTheory.TwV.DelA.targetFrameMap_eq_complexBlockAction_scalar_alt | exact GlobalTheory.TwV.DelA.targetFrameMap_eq_complexBlockAction_scalar_alt | (intros; apply GlobalTheory.TwV.DelA.targetFrameMap_eq_complexBlockAction_scalar_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnExistsChainChartsKernelDataFormsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumn_exists_chainCharts_kernelData_forms : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (C : ColsTiedSym (I.rec7 l Z)) (full : ColsFullS C) (g : Formalism.L2.G.GroupCompatibilityAll (I.rec7 l Z) hT ex.cmp), I.IsTw → ColIn.JetsIn I → ex.tw = I.tw l l0 Z → ex.errX.piT = X.piT → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) → I.StdC l Z C → I.StdDt l Z full.1.base.dt → g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → (∀ z : (I.rec7 l Z).Dt, ∃ r : (I.rec7 l Z).what₂.LL, (I.rec7 l Z).what₂.embLL r = (((I.rec7 l Z).chiD z : ℂˣ) : ℂ)) → ∀ (u : B.Word) (a : I.ι), Nonempty (GlobalTheory.Port.JIn t u a) := by
  first | exact @GlobalTheory.Port.jIn_nonempty_true | exact GlobalTheory.Port.jIn_nonempty_true | (intros; apply GlobalTheory.Port.jIn_nonempty_true <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitMulSourceScalarEqNextLevelScalar
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.DelA.unit_mul_scal_eq_scT : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), cKs S ι j hj La.1 La'.1 * (Formalism.L2.G.Pend.cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO d ι j La) * ι (d.uS S j La) * ι (d.uT S j La') = scT d S ι j La'.1 La'.2) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hpos ι hι
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  have hps := GlobalTheory.TwV.DelA.posTie_at S hpos ι hι
  intro d j hj La La'
  have hr := GlobalTheory.TwV.DelB.sysS_ranks S
  have hfr := GlobalTheory.T.changedFrame_rational_unitary S d j (Nat.le_of_succ_le hj) (hr.2.2.1 j) La
  have hsc := GlobalTheory.T.sourceScalar_latticeTuple_constant S d j hj ⟨La'.1⟩ La
  have hun := (GlobalTheory.T.stepDeterminantConstant_unit_independent S hpos ι hι j hj La.1 La'.1).2.1
  have hcA := GlobalTheory.TwV.DelA.scal_inv_frame (sysS H X std) D (hT.gat_pos u w hg) ℂ_[D.what₂.places.resChar w] ι (J.rho std) hps.1 d.fd2 j La (hr.2.2.1 j) (mM d j (Nat.le_of_succ_le hj) La) hfr.1 hfr.2.1
  have key : cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO d ι j La * ι (d.uS S j La) =
      ι (kS J j (Nat.le_of_succ_le hj) La.1 * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen) := by
    rw [hcA, sO, dif_pos (Nat.le_of_succ_le hj), ← map_mul, ← map_mul, ← hsc]
    congr 1
    unfold dPow
    ring
  rw [mul_assoc (cKs S ι j hj La.1 La'.1), key]
  unfold cKs scT
  rw [dif_pos hj, map_mul ι (kT J j hj La'.1), map_inv₀, map_mul ι (d.uT S j La')]
  have hy : ι (kS J j (Nat.le_of_succ_le hj) La.1 * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen) ≠ 0 := hun
  field_simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightParameter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts

namespace GlobalTheory

theorem weightParam_of_pin : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D := by
  intro hL D P
  exact GlobalTheory.T.weightInfinitesimalCharacterParam_of_levelCompatible D P.M P.tp.tup P.H.level (GlobalTheory.T.infinityType_etaTilde_at_cmTypeEmbeddings_eq_half D P.cf P.C P.tp P.chr) (GlobalTheory.T.infinitesimal_weight_of_dual D P.M P.tp.tup P.H)

end GlobalTheory
end

