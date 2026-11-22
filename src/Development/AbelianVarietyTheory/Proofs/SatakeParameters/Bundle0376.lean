import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0374
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0350
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0349
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0363
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0362
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0372
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0348
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0030
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import ReciprocityTheory.Hypotheses.GalCoh
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0032
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0270
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0356
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0360
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0364
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0366
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0369
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0370
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0375
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0358
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0371
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0347
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0342
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0344
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0367
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0151
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0343
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPStepCIff

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicDatumLevelEquivarianceFirstCoupledStepStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicDatum_level_equivariance_first_coupled_step : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i = t.m2 → PtAway A a i hi → LevAt A dtU a i hi) := by
  first | exact @GlobalTheory.AdLevCpl.levAt_coupled | exact GlobalTheory.AdLevCpl.levAt_coupled | (intros; apply GlobalTheory.AdLevCpl.levAt_coupled <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComparedFormNormalisedValuesLatticeTupleStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparedForm_normalisedValues_latticeTuple : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ x : ((ex.tw.fm u μ).lat (j + 1)).V, ∃ V : XR ((sysS H X std).Pj (j + 1)) ℂ, MvPolynomial.map (algebraMap (sysS H X std).G.Kf ℂ_[D.what₂.places.resChar w]) ((kaAt X H hT).cmp (j + 1) x La.1 La.2) = MvPolynomial.map ι V ∧ RealAt d (j + 1) hj h La ((ex.tw.fm u μ).emb (j + 1) x) V) := by
  first | exact @GlobalTheory.TwV.DelA.cmp_valsAt | exact GlobalTheory.TwV.DelA.cmp_valsAt | (intros; apply GlobalTheory.TwV.DelA.cmp_valsAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvenFrameBlockScalingHomogeneousPolynomialStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenFrameBlock_scaling_homogeneous_polynomial_alt : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (fd : FData X D) (c : Kc) (j : ℕ) (La' : X.Lt (j + 1)) (d : D.what₂.Tau → ℤ) (R : XspC (X.Pj (j + 1)) Kc), (∀ m ∈ R.support, ∀ τ, ¬ IsOddPos (pos.symm τ).2 → (∑ x : Var (X.Pj (j + 1)), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj (j + 1)).nV, Fin ((X.Pj (j + 1)).n' v)) = (posJ X D pos (j + 1)).symm τ then (m x : ℤ) else 0) = d τ) → GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') R = (∏ τ, if IsOddPos (pos.symm τ).2 then 1 else c ^ d τ) • GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.mk Kc fd j La') R := by
  first | exact @GlobalTheory.FrameB.evenFrameBlock_scaling_homogeneous_polynomial | exact GlobalTheory.FrameB.evenFrameBlock_scaling_homogeneous_polynomial | (intros; apply GlobalTheory.FrameB.evenFrameBlock_scaling_homogeneous_polynomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfinitesimalWeightOfDual
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts

namespace GlobalTheory.LocInfWt

theorem infWt_eq_infOf : ∀ (D : D7) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), HeckeOpen D M tup → ∀ (i : D.nd.Loc) (a : Formalism.L2.NG.AlgWt D.host.E D.R.nV) (τ : D.host.E →+* ℂ) (lam : Fin D.R.nV → ℤ), (M.loc i).wt.IsDual a → a.HWAt τ lam → D.naut.infWt i τ = Formalism.L2.NG.infOf lam := by
  intro D M tup hH i a τ lam hd hw
  obtain ⟨P, -⟩ := D.naut.pt_surj i (Classical.arbitrary (D.nd.X i))
  rw [D.nbc.embAV_inf i P, hH.emb i P,
    hH.au.wt (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (hH.av.rep i P) a hd]
  exact hH.au.infW (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 a τ lam hw

end GlobalTheory.LocInfWt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfinityTypeEtaTildeAtCmTypeEmbeddingsEqHalf
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts

namespace GlobalTheory.EtaInfType

theorem main : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C), NCharTied D cf C tp → ∀ t, D.naut.infG D.naut.etaT (Formalism.L2.embT D t) = {(1 / 2 : ℂ)} := by
  intro D cf C tp N t
  have hI : (N.e1 D.naut.etaT).1.HasInfQ (embPsi D.host) (fun _ => (1 / 2 : ℚ)) := by
    rw [N.etaT]
    exact ⟨fun _ => 1, fun _ => by norm_num, cf.isEta.inf⟩
  have h1 := (N.infG _ _ hI (D.eTau t)).1
  have e0 : Formalism.L2.embT D t = embPsi D.host (D.eTau t) := rfl
  rw [e0, h1]
  push_cast
  rfl

end GlobalTheory.EtaInfType
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteArithmeticGroupMove
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc

set_option maxHeartbeats 4000000 in

theorem site_move : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S =>
    S.Pos → S.Pair → S.Move) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS hPos hPair
  obtain ⟨hmm, -, hN, -⟩ := GlobalTheory.TwV.DelB.sysS_ranks S
  intro j hj c L La' γ hL hLa'
  rw [hmm] at hj
  have hr := hN j
  obtain ⟨g, κ, hM⟩ : ∃ g κ, MoveBy std J j hj.le c L γ g κ := by
    cases j with
    | zero => exact GlobalTheory.T.stepZero_latticeTuple_move_by_rational_isometry S hD hS c L γ hL
    | succ i => exact GlobalTheory.T.kernelSite_move_latticeTuple_at_succStep S hD hS i hj.le c L γ hL
  have hU := ((GlobalTheory.TwV.Xc.eMat_unitary_det _ _ (fun _ => rfl) _ _ hr _ _ (J.pins.crd_orth j hj.le)).2 g hM.1).1
  obtain ⟨hcq, hxi⟩ := GlobalTheory.T.movedDatum_movedLatticeTuple S hD hS j hj c L γ g κ hr hL hM La'
  refine ⟨eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g, _, hU, ?_,
    GlobalTheory.T.kernelLattice_movedLatticeTuple S hD hS j hj c L γ g κ hr hL hM, hcq, hxi, GlobalTheory.T.latticeTupleMove_scalar_power_of_p S hD hS hPos hPair j hj c L γ g κ hr hL hM La' hLa'⟩
  intro v
  rw [GlobalTheory.T.latticeTuple_frameMatrices_eq_of_same_component S hD hS j c (((sysS H X std).Lv.lev j c).smul γ L) L]
  exact hM.2.2.1 hr v

end GlobalTheory.TwV.Xc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteContractionIdentityOperatorHalf
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem delPolAt_site : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair → S.Pos → S.Law → ∀ (d : Dec J std), ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (Φ₀ : ∀ j, MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ →ₛₗ[ι] XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w]) (τ : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w] →ₗ[ℂ_[D.what₂.places.resChar w]] XspC ((sysS H X std).Pj (j + 1)) ℂ_[D.what₂.places.resChar w]) (sc : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → ℂ_[D.what₂.places.resChar w]) (sO : ∀ j, (sysS H X std).Lt j → ℂ_[D.what₂.places.resChar w]) (Gm : ∀ j, (sysS H X std).Lt j → ((ex.tw.fm u μ).lat j).V → ((sysS H X std).Pj j).Xsp), ∀ j < D.R.m, ∀ (cK : ℂ_[D.what₂.places.resChar w]) (hN : RankTie (sysS H X std) D j), MoveH S.Y u μ (kaAt X H hT).cmp (fun j La => glInv (sysS H X std) j (BOf d.fd2 j La)) Gm j → TieOpS (Y := S.Y) t u μ (clsAt X H) Gm sO j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) (ι := ι) (Φ₀ j) → KernelEntryDegreeCondition (Y := S.Y) t u μ (clsAt X H) j (eIdx (sysS H X std) D (hT.gat_pos u w hg) j hN) → DelYEqH S.Y (fun j La' => VOf ℂ_[D.what₂.places.resChar w] d.fd2 (ltC S.g S.hLT) j La') τ j → (∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → cK * (Formalism.L2.G.Pend.cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO j La) * ι (d.uS S j La) * ι (d.uT S j La') = sc j La'.1 La'.2) → DelPolAt (Y := S.Y) t u μ (clsAt X H) (kaAt X H hT).cmp (fun j => clsAt X H (j + 1)) (phiH D Φ₀ τ sc) (srOf S.Y) j cK) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hPair hPos hLaw d ι hι
  intro Φ₀ τ sc sO Gm j hj cK hN hMove hOp hDeg hDel hSc
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  have hR := GlobalTheory.T.siteSystem_ranks_eq_datum_ranks S
  have hFr := (GlobalTheory.T.siteFrames_and_changedFrames_invertible S).2 d
  have hSer := GlobalTheory.T.thetaSeries_site_eq_changedFrame_classSeries S hDict hPair hPos d ι hι j hj
  have hSerH := GlobalTheory.T.seriesCoefficients_at_kernelSite_of_classSeries S d ι j hN
  have hChi := GlobalTheory.T.kernelScalar_of_sourceTarget_parts_product S hDict d ι j hj (fun j La => Formalism.L2.G.Pend.cA (sysS H X std) ℂ_[D.what₂.places.resChar w] j (BOf d.fd2 j La) * sO j La) sc cK hSc
  exact GlobalTheory.T.contraction_identity_frames_with_operator_scalar t u μ _ (sysS H X std) S.E S.hfin S.hst S.g S.hLT (hT.gat_pos u w hg) d.fd2 (ltC S.g S.hLT)
    (fun j La La' => FrecG S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT (ltC S.g S.hLT) j La La')
    (d.gS S ι) hFr hLaw _ (clsAt X H) (kaAt X H hT).cmp (fun j => clsAt X H (j + 1)) ι Φ₀ τ sc (d.sH S ι) sO Gm j (hR.1 ▸ hj) cK hN
    hSer hMove hOp hDeg hSerH hChi hDel

end GlobalTheory.TwV.DelB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteLatticeTuplePairsAdmissible
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
open Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem pairOK_allSites : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pair) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD
  intro j hj La La' hL hL'
  have hm : (sysS H X std).mm = D.R.m := by
    first | (rfl; done) | exact X.fl_m | exact I.fl_m
  have hjm : j + 1 ≤ D.R.m := hm ▸ hj
  have hSD0 := GlobalTheory.T.kernelLattice_selfDual_even_rank_at_site t std J hD j (by omega) La hL
  have hSD1 := GlobalTheory.T.kernelLattice_selfDual_even_rank_at_site t std J hD (j + 1) hjm La' hL'
  have hA : TaylorLogMetric.admitted D _ _ ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La') := ⟨hSD0.1, hSD1.1, hSD0.2, hSD1.2⟩
  have hInt : ∀ x, IntOff (t.O u μ).S (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' x) :=
    fun x => GlobalTheory.T.intOff_xi0_of_joint t std J S j La La' _
  have hK := GlobalTheory.kerTh_entire_algCoef D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok (ssRec t u μ) (t.rd u μ).lev _ _ _
    (t.O u μ).S hA (GlobalTheory.T.site_finite_data_level_pos_bad_prime_factors t std J) hInt
  have hC := (GlobalTheory.SelfDualChiAlg.chi_detId_and_chiFac_alg D t.χ t.χ_ok).2 _ _ hA
  have hsp : ∀ (i : ℕ) (hi : i ≤ D.R.m) (Lb : (sysS H X std).Lt i), ((sysS H X std).Pj i).IsLatTup Lb.2 → ∀ v,
      locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN i Lb) =
        ((sysS H X std).latAt v i Lb.2).map ((((J.fd std).frM i Lb v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
    intro i hi Lb hLb v
    cases i with
    | zero => exact GlobalTheory.T.frame_localLattice_span_kernelLattice_zero t std J hD Lb hLb v
    | succ k => exact GlobalTheory.T.frame_localLattice_span_kernelLattice_succ t std J hD k hi Lb hLb v
  refine ⟨hA, GlobalTheory.T.movedPairDatum_congr t std J S hD j hj La La' hL hL', hK.1, hK.2, GlobalTheory.T.latticeTuplePairScalar_mem_algebraicClosure t std J S hD j hj La La' hL hL',
    hC.1, hC.2, fun v => ⟨?_, ?_, hsp j (by omega) La hL v, hsp (j + 1) hjm La' hL' v⟩⟩
  · exact GlobalTheory.isUnit_det_frameMatrix_ofCharts (J.cp std) J.a ∅ j La v
  · exact GlobalTheory.isUnit_det_frameMatrix_ofCharts (J.cp std) J.a ∅ (j + 1) La' v

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteScalarsAgreeAwayFromPlace
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.Xc.AwayId

theorem key {K : Type} [Field K] {P M C : K} (hP : P ≠ 0) (hM : M ≠ 0) (hC : C ≠ 0) (V A A' n n' : ℤ) :
    P ^ (V * (n - n')) * (M ^ n' * (M ^ n)⁻¹ * (C ^ n) ^ (-A) * (C ^ n') ^ A') * (P ^ (-V) * (M * C ^ A)) ^ n *
      (P ^ V * (M⁻¹ * C ^ (-A'))) ^ n' = 1 := by
  simp only [mul_zpow, ← zpow_mul, inv_zpow', mul_sub, zpow_sub₀ hP, neg_mul, zpow_neg]
  rw [mul_comm A n, mul_comm A' n', mul_comm V n, mul_comm V n']
  field_simp

theorem map_zpow_of {G M : Type*} [Group G] [DivisionMonoid M] (f : G → M) (U : Subgroup G) (h1 : f 1 = 1)
    (hm : ∀ x ∈ U, ∀ y ∈ U, f (x * y) = f x * f y) {x : G} (hx : x ∈ U) (n : ℤ) : f (x ^ n) = f x ^ n := by
  let φ : U →* M := { toFun := fun y => f y, map_one' := h1, map_mul' := fun y z => hm _ y.2 _ z.2 }
  have := map_zpow φ ⟨x, hx⟩ n
  simpa [φ] using this

theorem lamC_mul' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x * y) = TaylorLogMetric.lamC lam x * TaylorLogMetric.lamC lam y := by
  rw [lamC_eq_of_mem lam hx, lamC_eq_of_mem lam hy, lamC_eq_of_mem lam (mul_mem hx hy), ← map_mul]
  rfl

theorem lamC_zpow' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (n : ℤ) :
    TaylorLogMetric.lamC lam (x ^ n) = TaylorLogMetric.lamC lam x ^ n := by
  rw [lamC_eq_of_mem lam hx, lamC_eq_of_mem lam (zpow_mem hx n), ← map_zpow₀]
  rfl

theorem lamC_inv' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam x⁻¹ = (TaylorLogMetric.lamC lam x)⁻¹ := by
  rw [lamC_eq_of_mem lam hx, lamC_eq_of_mem lam (inv_mem hx), ← map_inv₀]
  rfl

theorem lamC_ne_zero' {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {x : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (h0 : x ≠ 0) :
    TaylorLogMetric.lamC lam x ≠ 0 := by
  rw [lamC_eq_of_mem lam hx]
  exact (map_ne_zero lam).2 fun h => h0 (congrArg Subtype.val h)

theorem final {K : Type} [Field K] {P M C Q s : K} (hP : P ≠ 0) (hM : M ≠ 0) (hC : C ≠ 0) (V A A' la la' n n' : ℤ) :
    Q * P ^ (V * (n - n')) * (s * (M ^ n' * (M ^ n)⁻¹ * (C ^ n) ^ (-A) * (C ^ n') ^ A')) *
        ((P ^ (-V) * (M * C ^ A)) ^ (la + n) * (P ^ V * (M⁻¹ * C ^ (-A'))) ^ (la' + n')) =
      Q * s * ((P ^ (-V) * (M * C ^ A)) ^ la * (P ^ V * (M⁻¹ * C ^ (-A'))) ^ la') := by
  have hXa : P ^ (-V) * (M * C ^ A) ≠ 0 := mul_ne_zero (zpow_ne_zero _ hP) (mul_ne_zero hM (zpow_ne_zero _ hC))
  have hXb : P ^ V * (M⁻¹ * C ^ (-A')) ≠ 0 := mul_ne_zero (zpow_ne_zero _ hP) (mul_ne_zero (inv_ne_zero hM) (zpow_ne_zero _ hC))
  have hk := key hP hM hC V A A' n n'
  rw [zpow_add₀ hXa, zpow_add₀ hXb]
  calc _ = Q * s * ((P ^ (-V) * (M * C ^ A)) ^ la * (P ^ V * (M⁻¹ * C ^ (-A'))) ^ la') *
        (P ^ (V * (n - n')) * (M ^ n' * (M ^ n)⁻¹ * (C ^ n) ^ (-A) * (C ^ n') ^ A') * (P ^ (-V) * (M * C ^ A)) ^ n *
          (P ^ V * (M⁻¹ * C ^ (-A'))) ^ n') := by ring
    _ = _ := by rw [hk, mul_one]

set_option maxHeartbeats 4000000 in

theorem scal_away : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pair → ∀ v π, IsUnifAt J v π → ∀ j < D.R.m, ∀ a b : (sysS H X std).G.Kf, S.E.iK a = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ (-((sysS H X std).vm v (j + 1))) * TaylorLogMetric.lamC S.lam (S.muT (j + 1) π * chiI J π ^ (((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) → S.E.iK b = ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ ((sysS H X std).vm v (j + 1)) * TaylorLogMetric.lamC S.lam ((S.muT (j + 1) π)⁻¹ * chiI J π ^ (-((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ)))) → ∀ (La Lb : (sysS H X std).Lt j) (La' Lb' : (sysS H X std).Lt (j + 1)), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → SameAway (hT := hT) (H := H) (X := X) std v (j + 1) La' Lb' → GlobalTheory.TwU.pPow (sysS H X std) j La La' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j La La') * S.E.iK (a ^ len (sysS H X std) v j Lb.2 * b ^ len (sysS H X std) v (j + 1) Lb'.2) = GlobalTheory.TwU.pPow (sysS H X std) j Lb Lb' * TaylorLogMetric.lamC S.lam (GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j Lb Lb') * S.E.iK (a ^ len (sysS H X std) v j La.2 * b ^ len (sysS H X std) v (j + 1) La'.2)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hSpl hP v π hπ j hj a b ha hb La Lb La' Lb' hab hab'
  have hR := GlobalTheory.TwV.DelB.sysS_ranks S
  have hjle : j ≤ D.R.m := hj.le
  have hj1 : j + 1 ≤ D.R.m := hj
  have hjm : j < (sysS H X std).mm := hR.1 ▸ hj
  have hPa := hP j hjm La La' hab.1 hab'.1
  have hPb := hP j hjm Lb Lb' hab.2.1 hab'.2.1
  obtain ⟨k, hkU, hkI, hkO, hk⟩ := GlobalTheory.T.det_latticeTuples_agreeing_away_from_place S hD hSpl v π hπ j hjle La Lb hab
  obtain ⟨k', hkU', hkI', hkO', hk'⟩ := GlobalTheory.T.det_latticeTuples_agreeing_away_from_place S hD hSpl v π hπ (j + 1) hj1 La' Lb' hab'
  obtain ⟨c0, hc0⟩ := GlobalTheory.T.kernelLattice_detIdeal_character_eq_const_mul_det S hD hSpl j hjle
  obtain ⟨c0', hc0'⟩ := GlobalTheory.T.kernelLattice_detIdeal_character_eq_const_mul_det S hD hSpl (j + 1) hj1
  obtain ⟨-, hsl⟩ := GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway S hD hSpl v j hjle La Lb hab
  obtain ⟨-, hsl'⟩ := GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway S hD hSpl v (j + 1) hj1 La' Lb' hab'
  obtain ⟨hχm, hχ1, -, hχN⟩ := GlobalTheory.T.charOnNormOneIdeles_mul_unramified_classValue S hD hSpl
  have hbad := (GlobalTheory.T.level_badPrimes_coprime_residueChar S hD hSpl).2.2.2
  have hdtb := (GlobalTheory.T.lattice_det_mem_U1_and_ordA_eq_neg_len S hD hSpl j hjle Lb hab.2.1).1
  have hdtb' := (GlobalTheory.T.lattice_det_mem_U1_and_ordA_eq_neg_len S hD hSpl (j + 1) hj1 Lb' hab'.2.1).1
  have law := S.law
  have hmuk : ∀ κ ∈ U1 (sigD D), κ ∈ intU D.host.F D.host.E → OneOff ((A0 J).pl v).1 κ → S.muT (j + 1) κ = 1 := by
    intro κ hκ hκI hκO
    refine law.mu_unr j hj κ hκ hκI fun v' hv' => hκO v' fun h => hbad v' hv' ?_
    rw [h]
    exact ((A0 J).pl v).2

  have hmuF : ∀ x ∈ U1 (sigD D), ∀ (e : ℤ) (κ : (AfE D.host.F D.host.E)ˣ), κ ∈ U1 (sigD D) → S.muT (j + 1) κ = 1 →
      S.muT (j + 1) (x * π ^ e * κ) = S.muT (j + 1) x * S.muT (j + 1) π ^ e := by
    intro x hx e κ hκ h1
    have hpe : π ^ e ∈ U1 (sigD D) := zpow_mem hπ.1 e
    rw [(law.mu_mul j hj).2 _ (mul_mem hx hpe) _ hκ, h1, mul_one, (law.mu_mul j hj).2 _ hx _ hpe,
      map_zpow_of (S.muT (j + 1)) (U1 (sigD D)) (law.mu_mul j hj).1 (law.mu_mul j hj).2 hπ.1 e]
  have hchi1 : chiI J 1 = 1 := hχ1 1 (one_mem _) (one_mem _)
  have hchF : ∀ x ∈ U1 (sigD D), ∀ (e : ℤ) (κ : (AfE D.host.F D.host.E)ˣ), κ ∈ U1 (sigD D) → κ ∈ intU D.host.F D.host.E →
      chiI J (x * π ^ e * κ) = chiI J x * chiI J π ^ e := by
    intro x hx e κ hκ hκI
    have hpe : π ^ e ∈ U1 (sigD D) := zpow_mem hπ.1 e
    rw [hχm _ (mul_mem hx hpe) _ hκ, hχ1 κ hκ hκI, mul_one, hχm _ hx _ hpe, map_zpow_of (chiI J) (U1 (sigD D)) hchi1 hχm hπ.1 e]
  have hscal : GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j La La' =
      GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j Lb Lb' *
        (S.muT (j + 1) π ^ (len (sysS H X std) v (j + 1) Lb'.2 - len (sysS H X std) v (j + 1) La'.2) *
          (S.muT (j + 1) π ^ (len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2))⁻¹ *
          (chiI J π ^ (len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2)) ^ (-(((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) *
          (chiI J π ^ (len (sysS H X std) v (j + 1) Lb'.2 - len (sysS H X std) v (j + 1) La'.2)) ^ ((((j + 1) * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ))) := by
    unfold GlobalTheory.TwU.scal0
    rw [hc0 La hab.1 hPa.1.2.2.1, hc0 Lb hab.2.1 hPb.1.2.2.1, hc0' La' hab'.1 hPa.1.2.2.2, hc0' Lb' hab'.2.1 hPb.1.2.2.2, hk, hk',
      hmuF _ hdtb _ k hkU (hmuk k hkU hkI hkO), hmuF _ hdtb' _ k' hkU' (hmuk k' hkU' hkI' hkO'),
      hchF _ hdtb _ k hkU hkI, hchF _ hdtb' _ k' hkU' hkI']
    simp only [mul_zpow, mul_inv]
    ring

  have hp0 : ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ≠ 0 :=
    Nat.cast_ne_zero.2 (Fact.out : (D.what₂.places.resChar w).Prime).ne_zero
  have hpp : GlobalTheory.TwU.pPow (sysS H X std) j La La' = GlobalTheory.TwU.pPow (sysS H X std) j Lb Lb' *
      ((D.what₂.places.resChar w : ℕ) : ℂ_[D.what₂.places.resChar w]) ^ ((sysS H X std).vm v (j + 1) *
        ((len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2) -
          (len (sysS H X std) v (j + 1) Lb'.2 - len (sysS H X std) v (j + 1) La'.2))) := by
    unfold GlobalTheory.TwU.pPow
    rw [← zpow_add₀ hp0]
    congr 1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v), ← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
    have he : ∀ v' ∈ Finset.univ.erase v, (sysS H X std).vm v' (j + 1) * (len (sysS H X std) v' (j + 1) La'.2 - len (sysS H X std) v' j La.2) =
        (sysS H X std).vm v' (j + 1) * (len (sysS H X std) v' (j + 1) Lb'.2 - len (sysS H X std) v' j Lb.2) := by
      intro v' hv'
      rw [hsl v' (Finset.ne_of_mem_erase hv'), hsl' v' (Finset.ne_of_mem_erase hv')]
    rw [Finset.sum_congr rfl he]
    ring

  have hm_alg : S.muT (j + 1) π ∈ TaylorLogMetric.Qbar := law.mu_alg j hj π hπ.1
  have hm_ne : S.muT (j + 1) π ≠ 0 := law.mu_ne hj hπ.1
  obtain ⟨𝔞, hN1, hc𝔞⟩ := hχN π hπ.1
  have hgx := GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg
  have hcu := GlobalTheory.TwV.Xc.chi_alg_unit_inert D _ S.lam t.χ t.χ_ok (by omega) hgx.2.1 𝔞 hN1
  have hc_alg : chiI J π ∈ TaylorLogMetric.Qbar := hc𝔞 ▸ hcu.1
  have hc_ne : chiI J π ≠ 0 := hc𝔞 ▸ hcu.2.1
  have hsb : GlobalTheory.TwU.scal0 (sysS H X std) (J.fd std) t.χ S.muT j Lb Lb' ∈ TaylorLogMetric.Qbar := hPb.2.2.2.2.1
  have hLm := lamC_ne_zero' S.lam hm_alg hm_ne
  have hLc := lamC_ne_zero' S.lam hc_alg hc_ne
  have hma := fun (e : ℤ) => zpow_mem hm_alg e
  have hca := fun (e : ℤ) => zpow_mem hc_alg e
  rw [lamC_mul' S.lam hm_alg (hca _), lamC_zpow' S.lam hc_alg] at ha
  rw [lamC_mul' S.lam (inv_mem hm_alg) (hca _), lamC_inv' S.lam hm_alg, lamC_zpow' S.lam hc_alg] at hb
  rw [hpp, hscal, lamC_mul' S.lam hsb (mul_mem (mul_mem (mul_mem (hma _) (inv_mem (hma _))) (zpow_mem (hca _) _)) (zpow_mem (hca _) _)),
    lamC_mul' S.lam (mul_mem (mul_mem (hma _) (inv_mem (hma _))) (zpow_mem (hca _) _)) (zpow_mem (hca _) _),
    lamC_mul' S.lam (mul_mem (hma _) (inv_mem (hma _))) (zpow_mem (hca _) _),
    lamC_mul' S.lam (hma _) (inv_mem (hma _)), lamC_inv' S.lam (hma _),
    lamC_zpow' S.lam (hca _), lamC_zpow' S.lam (hca _), lamC_zpow' S.lam hm_alg, lamC_zpow' S.lam hm_alg,
    lamC_zpow' S.lam hc_alg, lamC_zpow' S.lam hc_alg,
    map_mul, map_mul, map_zpow₀, map_zpow₀, map_zpow₀, map_zpow₀, ha, hb]
  have e1 : len (sysS H X std) v j Lb.2 = len (sysS H X std) v j La.2 + (len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2) := by ring
  have e2 : len (sysS H X std) v (j + 1) Lb'.2 = len (sysS H X std) v (j + 1) La'.2 +
      (len (sysS H X std) v (j + 1) Lb'.2 - len (sysS H X std) v (j + 1) La'.2) := by ring
  generalize len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2 = n at e1 ⊢
  generalize len (sysS H X std) v (j + 1) Lb'.2 - len (sysS H X std) v (j + 1) La'.2 = n' at e2 ⊢
  rw [e1, e2]
  exact final hp0 hLm hLc _ _ _ _ _ _ _
end GlobalTheory.TwV.Xc.AwayId

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleFrameScalarOddPositionsDetStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTupleFrame_scalar_oddPositions_det : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (c : Kc), c ≠ 0 → ∀ (j : ℕ) (hN : RankTie X D j) (La' : X.Lt (j + 1)) (M : GL (Fin (D.R.N (j + 1))) D.host.E), StdU D M → FrIs fd ρ (j + 1) La' (rkT X D hN) M → ∀ (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → GlobalTheory.FrameB.sS X Kc j (GlobalTheory.FrameB.kV Kc fd c j La') * GlobalTheory.FrameB.kN X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') (GlobalTheory.FrameB.kV Kc fd c j La') * (GlobalTheory.FrameB.kD X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') (GlobalTheory.FrameB.kV Kc fd c j La'))⁻¹ = ∏ τ, if IsOddPos (pos.symm τ).2 then c ^ szT X D pos j τ * ι (embT D τ (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det) ^ cT1 X D pos j τ else 1 := by
  first | exact @GlobalTheory.TwV.DelA.scal_tauV | exact GlobalTheory.TwV.DelA.scal_tauV | (intros; apply GlobalTheory.TwV.DelA.scal_tauV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleReadingEqOfRealisingPolynomialStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTupleReading_eq_of_realising_polynomial : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ (φ : (D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) (V : XR ((sysS H X std).Pj (j + 1)) ℂ), (∀ d : Dec J std, RealAt d (j + 1) hj h La φ V) → rdJ I X.onCh ι j La.1 La.2 φ = MvPolynomial.map ι V) := by
  first | exact @GlobalTheory.TwV.DelA.rdJ_eq_of_realAt | exact GlobalTheory.TwV.DelA.rdJ_eq_of_realAt | (intros; apply GlobalTheory.TwV.DelA.rdJ_eq_of_realAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SourceScalarLatticeTupleConstant
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem source_scalar_const : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j < D.R.m), Nonempty (Lv.comp (j + 1)) → ∀ La : (sysS H X std).Lt j, dPow (mM d j hj.le La).1 (fun τ => -(wT (sysS H X std) D (hT.gat_pos u w hg) j τ)) * sPt d j hj.le La * d.uS S j La = kS J j hj.le La.1) := by
  unfold GlobalTheory.TwV.AllSites
  intro D _ hT _ _ _ _ _ ex u μ w hg Lv I H X _ std t J S d j hj hne La
  have hW := GlobalTheory.T.kernelSite_modelStageWeights_eq_chainWeights S j hj hne
  have hfr := (GlobalTheory.T.changedFrame_rational_unitary S d j hj.le (rkS _ _ hW.rk) La).2.2
  obtain ⟨e, he, hmu⟩ := GlobalTheory.T.stepCharacter_det_rationalIsometry S j hj
  have hgd := (GlobalTheory.T.det_rational_unitary_orthonormalChange_matrices S j hj.le).2 _ (d.mem j hj.le La)
  obtain ⟨q, hq⟩ := Formalism.L2.Ker.even_rankN D.R (j + 1)
  have hs : ∀ τ, (D.chTw u μ).sSharp j τ = e τ - ((D.R.N (j + 1) / 2 : ℕ) : ℤ) := by
    intro τ
    have h1 := (D.chTw u μ).sSharp_eq j hj τ
    rw [D.hcW_e u τ, ← he τ] at h1
    have h2 : D.R.N (j + 1) / 2 = q := by omega
    rw [h2]
    have h3 : ((D.R.N (j + 1) : ℕ) : ℚ) = (q : ℚ) + q := by exact_mod_cast hq
    unfold sExp' at h1
    rw [h3] at h1
    have h4 : ((D.chTw u μ).sSharp j τ : ℚ) = ((e τ - (q : ℤ) : ℤ) : ℚ) := by push_cast; rw [h1]; ring
    exact_mod_cast h4
  have hχ : d.chi j hj.le La ≠ 0 := by unfold Dec.chi; exact Units.ne_zero _
  have hcD : ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  unfold dPow sPt Dec.uS kS dPow
  rw [dif_pos hj.le, hmu j hj.le _ (d.mem j hj.le La), hgd.1]
  simp only []
  set n : ℤ := ((D.R.N (j + 1) / 2 : ℕ) : ℤ) with hn
  set c : ℤ := cTw D j with hc
  rw [show ∀ (A χ C B Mu P : ℂ), A * (χ * C ^ c * B) * (χ⁻¹ * Mu⁻¹ * P * C ^ (-c)) = A * B * Mu⁻¹ * P * (χ * χ⁻¹) * (C ^ c * C ^ (-c)) from
    fun _ _ _ _ _ _ => by ring]
  rw [mul_inv_cancel₀ hχ, ← zpow_add₀ hcD, add_neg_cancel, zpow_zero, mul_one, mul_one]
  rw [← Finset.prod_zpow, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hm : (embT D τ) (mM d j hj.le La).1.det ≠ 0 := by rw [map_ne_zero]; exact (Matrix.isUnits_det_units _).ne_zero
  have hgn : (embT D τ) (d.gam j hj.le La).1.det ≠ 0 := by rw [map_ne_zero]; exact (Matrix.isUnits_det_units _).ne_zero
  have hb := congrArg (embT D τ) hfr
  rw [map_mul] at hb
  rw [← hb, hW.sh τ, hs τ]
  show (embT D τ) _ ^ _ * _ * ((embT D τ) _ ^ _)⁻¹ * ((embT D τ) (_ * _)) ^ _ = _
  rw [map_mul]
  generalize (embT D τ) (mM d j hj.le La).1.det = m at hm ⊢
  generalize (embT D τ) (d.gam j hj.le La).1.det = g at hgn ⊢
  generalize (embT D τ) (gMat J j hj.le 1).det = G
  generalize e τ = ee
  simp only [mul_zpow, zpow_neg, zpow_sub₀ hm, zpow_sub₀ hgn, zpow_add₀ hm, zpow_add₀ hgn]
  field_simp
  ring

end GlobalTheory.TwV.DelA
end

