import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0365
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0032
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0283
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0298
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0342
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0349
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0368
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0367
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0362
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0270
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0366
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0278
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0333
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0301

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChangedFrameEqCoordMulInvMulBasisStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frM_eq_map_crd_mul_gam_inv_mul_basis : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) La v, d.fd2.frM j La v = (((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E).submatrix (Fin.cast hr) (Fin.cast hr) * ((J.cp std).B j La).1.submatrix (Fin.cast ((J.cp std).hk j La)) (Fin.cast ((J.cp std).hk j La))).map (J.rho std v)) := by
  first | exact @GlobalTheory.TwV.DelB.changedFrame_eq_coord_mul_inv_mul_basis | exact GlobalTheory.TwV.DelB.changedFrame_eq_coord_mul_inv_mul_basis | (intros; apply GlobalTheory.TwV.DelB.changedFrame_eq_coord_mul_inv_mul_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBasePointRightTranslateByChartLevelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartBasePoint_rightTranslate_by_chartLevel : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p (κ : ((St i hi).K β).lev.U), x'.1 = x.1 * κ.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p') := by
  first | exact @GlobalTheory.TwV.isPtAd_mul_lev | exact GlobalTheory.TwV.isPtAd_mul_lev | (intros; apply GlobalTheory.TwV.isPtAd_mul_lev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComparedFormLevelZeroRealisesComplexPolyStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparedForm_levelZero_realises_complexPoly : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) (h : ((sysS H X std).Pj 0).m + 1 = D.R.N 0) (La : (sysS H X std).Lt 0), ((sysS H X std).Pj 0).IsLatTup La.2 → ∀ x : ((ex.tw.fm u μ).lat 0).V, ∃ V : XR ((sysS H X std).Pj 0) ℂ, MvPolynomial.map (algebraMap (sysS H X std).G.Kf ℂ_[D.what₂.places.resChar w]) ((kaAt X H hT).cmp 0 x La.1 La.2) = MvPolynomial.map ι V ∧ RealAt d 0 (Nat.zero_le _) h La ((ex.tw.fm u μ).emb 0 x) V) := by
  first | exact @GlobalTheory.TwV.DelA.cmp_realAt_zero | exact GlobalTheory.TwV.DelA.cmp_realAt_zero | (intros; apply GlobalTheory.TwV.DelA.cmp_realAt_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOffPrimeKernelLatticesOfAgreeAwayStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eqOffPrime_kernelLattices_of_agreeAway : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ v (P : HeightOneSpectrum (𝓞 D.host.E)), PrimeOf (D.what₂.places.resChar w) ((sysS H X std).G.P.W v) (J.rho std v) P → ∀ j (hj : j ≤ D.R.m) (La Lb : (sysS H X std).Lt j), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → GL3Theta.EqOff D P ((J.fd std).kerN j La) ((J.fd std).kerN j Lb)) := by
  first | exact @GlobalTheory.TwV.Xc.eqOff_kerN_of_sameAway | exact GlobalTheory.TwV.Xc.eqOff_kerN_of_sameAway | (intros; apply GlobalTheory.TwV.Xc.eqOff_kerN_of_sameAway <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComparisonSiteDataOverChainChartsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_comparisonSiteData_over_chainCharts : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (μ : D.what₂.Tup) (J : JIn t u μ), (D.what₂.places.resChar w) ∉ Dx.Qp μ → ∃ Z : SiteD J.Gd.herm u w hg (ex.tw.fm u μ), Z.Fo = foOf J.Hh J.St J.val ∧ SiteGood Z ∧ SiteRest Z ex.cmp ∧ ∀ i hi, Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E (Z.S i hi).B = (J.A.crd (i + 1) hi)⁻¹ := by
  first | exact @GlobalTheory.SiteEx.siteD_exists | exact GlobalTheory.SiteEx.siteD_exists | (intros; apply GlobalTheory.SiteEx.siteD_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepAdelicDatumLawTargetLevelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstCoupledStep_adelicDatum_law_targetLevel : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i = t.m2 → PtAway A a i hi →
  ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' x₁' : UA D (i + 1) hi) (κ' : ((St (i + 1) hi).K β').lev.U) p p' p₁',
    x₁'.1 = x'.1 * κ'.1 → IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
    IsPtAd A a (i + 1) hi β' x₁' p₁' → ∀ w,
    muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * t.seam.σ₀ (xiPt A i hi β β' p p₁' w) =
      ((((St (i + 1) hi).K β').lev.chi κ' : ℂˣ) : ℂ) * t.seam.σ₀ (xiPt A i hi β β' p p' w)) := by
  first | exact @GlobalTheory.CplTarget.levAt_target | exact GlobalTheory.CplTarget.levAt_target | (intros; apply GlobalTheory.CplTarget.levAt_target <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepAdelicDatumSourceLevelLaw
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.LevSrcCpl

section Local
variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

open GlobalTheory.TopLaw GlobalTheory.CoupledLaw in

theorem firstCoupledDatum_source_level_law {u : Pr.Word} (hX : X.Ok) (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) {al : L.β m2}
    {p q : ChPt (R := R) sel mu u m2} (p' : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1))))
    {κ : GLQ X.E (R.N m2) (rowSG Pr sel mu)} {c : rowSG Pr sel mu → X.Kˣ}
    (hκ : ∀ P, frsF sel mu q P = frsF sel mu p P * ((κ P)⁻¹).1)
    (ha : ∀ P, LevAt (L.levG m2 al) (L.levQ m2 al) P (κ P) (c P))
    (hN : q.deco.1.N = p.deco.1.N) (hf : q.deco.1.f = p.deco.1.f) (x : HomE X.E (R.N m2) (R.N (m2 + 1))) :
    XiCpl1 Ch sel mu cst L m2 al q p' Y x * ∏ P : rowSG Pr sel mu, rhoS Ch sel mu m2 P ((LinearEquiv.det ((κ P)⁻¹).1 : X.Eˣ) : X.E) =
      (((∏ P, c P)⁻¹ : X.Kˣ) : X.K) * XiCpl1 Ch sel mu cst L m2 al p p' Y x := by
  have e0 : phiT X.K q.deco.1 p'.deco.1 x = phiT X.K p.deco.1 p'.deco.1 x := by
    unfold phiT Deco.at
    rw [hN, hf]
  unfold XiCpl1
  rw [e0, mul_assoc, mul_left_comm _ (phiT _ _ _ _), ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, Units.coe_prod,
    ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun P _ => ?_)
  have e1 : inFr (frsF sel mu q P) (frsF sel mu p' P) x =
      inFr (frsF sel mu p P) (frsF sel mu p' P) x ∘ₗ ((κ P)⁻¹).1.toLinearMap := by
    rw [hκ]
    rfl
  rw [e1]
  exact psiAt_source hX hPr hL (ha P).inv _ _

end Local
end GlobalTheory.LevSrcCpl

namespace GlobalTheory.LevSrcCpl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem levSrc_cpl : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i = t.m2 → PtAway A a i hi →
  ∀ β β' (x x₁ : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) (κ : ((St i (Nat.le_of_succ_le hi)).K β).lev.U) p p' p₁,
    x₁.1 = x.1 * κ.1 → IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
    IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p₁ → ∀ w,
    ((((St i (Nat.le_of_succ_le hi)).K β).lev.chi κ : ℂˣ) : ℂ) * t.seam.σ₀ (xiPt A i hi β β' p₁ p' w) =
      muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (xiPt A i hi β β' p p' w)) := by
  unfold GlobalTheory.TwV.UnderTie
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie _hEx hMu i hi hi2 hAway β β' x x₁ x' κ p p' p₁ hx hp hp' hp₁ w
  subst hi2
  have hlt : t.m2 < D.R.m := hi
  obtain ⟨g, z, hgz, hchi⟩ := GlobalTheory.T.firstCoupledStep_level_local_elements_values A dtU a hPins hTie hlt β κ
  obtain ⟨q, κP, c, hfr, hlev, hN, hf, hcz, hrho, hin⟩ := GlobalTheory.T.exists_chart_point_frames_moved_by_level A dtU a hPins hTie hlt β κ p g z hgz
  have hq : IsPtAd A a t.m2 hlt.le β x₁ q :=
    GlobalTheory.T.chart_base_point_adelic_right_mul_level A dtU a hPins hTie t.m2 hlt.le β κ x x₁ p q (fun P => ((κP P)⁻¹).1) hx hp hN hf hfr (fun P => ((κP P)⁻¹).2) hin
  have hD := GlobalTheory.T.firstCoupledStepCharacter_at_levelDet_mul_tameValues A dtU a hPins hTie hMu hlt β κ g z hgz
  have eA : xiPt A t.m2 hi β β' p₁ p' w = xiPt A t.m2 hi β β' q p' w :=
    congrFun (hAway β β' x₁ x' x₁ x' q p' p₁ p' hq hp' hp₁ hp' (fun _ _ => ⟨rfl, rfl⟩)) w
  rw [eA]
  unfold xiPt
  rw [dif_neg (lt_irrefl _), if_pos rfl, dif_neg (lt_irrefl _), if_pos rfl]
  have hsrc := firstCoupledDatum_source_level_law (G := t.glob) (cst := t.cst μ) (Ch := t.Ch) hPins.fields.ok t.pr_ok (t.idx_ok μ) (al := A.ib t.m2 hlt β) p'
    (cosetOf A (t.m2 + 1) hi β' p') hfr hlev hN hf w
  have hprod : ((∏ P, c P : t.X.Kˣ) : t.X.K) * ∏ P, z P = 1 := by
    rw [Units.coe_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun P _ => hcz P
  simp_rw [hrho] at hsrc
  have e4 := congrArg t.seam.σ₀ hsrc
  have e2 := congrArg t.seam.σ₀ hprod
  have e3 : t.seam.σ₀ (((∏ P, c P)⁻¹ : t.X.Kˣ) : t.X.K) * t.seam.σ₀ ((∏ P, c P : t.X.Kˣ) : t.X.K) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [map_mul, map_mul] at e4
  rw [map_mul, map_one] at e2
  linear_combination (t.seam.σ₀ (XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hlt β) q p' (cosetOf A (t.m2 + 1) hi β' p') w) *
      t.seam.σ₀ ((∏ P, c P : t.X.Kˣ) : t.X.K)) * hchi
    - (t.seam.σ₀ (XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hlt β) q p' (cosetOf A (t.m2 + 1) hi β' p') w) *
      ((((St t.m2 hlt.le).K β).lev.chi κ : ℂˣ) : ℂ)) * e2
    - (t.seam.σ₀ ((∏ P, c P : t.X.Kˣ) : t.X.K) *
      t.seam.σ₀ (XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hlt β) q p' (cosetOf A (t.m2 + 1) hi β' p') w)) * hD
    + (muOf t u μ dtU (t.m2 + 1) (Matrix.GeneralLinearGroup.det κ.1) *
      t.seam.σ₀ (XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hlt β) p p' (cosetOf A (t.m2 + 1) hi β' p') w)) * e3
    + (muOf t u μ dtU (t.m2 + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ ((∏ P, c P : t.X.Kˣ) : t.X.K)) * e4

end GlobalTheory.LevSrcCpl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FramePolynomialsWeightRealisedNextLevel
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwV.DelA

theorem sgRev_mul_self_eq_one (n : ℕ) : sgRev n * sgRev n = 1 := by
  unfold sgRev
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n))) with h | h <;> rw [h] <;> norm_num

theorem sgRev_ne_zero_of_sq (n : ℕ) : sgRev n ≠ 0 := fun h => by simpa [h] using sgRev_mul_self_eq_one n

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem det_zT_of_odd {n : ℕ}
    (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (ho : IsOddPos (pos.symm τ).2) :
    (zT X D pos f τ).det = sgRev n * ((f τ).det)⁻¹ := by
  unfold zT
  rw [if_pos ho]
  have : (((f τ)⁻¹).transpose.submatrix id Fin.rev) = (((f τ)⁻¹).transpose.submatrix id (Fin.revPerm : Equiv.Perm (Fin n))) := rfl
  rw [this, Matrix.det_permute', Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  rfl

theorem det_zT_of_even {n : ℕ}
    (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) (τ : D.what₂.Tau) (ho : ¬ IsOddPos (pos.symm τ).2) :
    (zT X D pos f τ).det = (f τ).det := by
  unfold zT
  rw [if_neg ho]

def frVarToModel (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (k : GL3Theta.FrV D n) : Var (X.Pj i) :=
  ⟨((posJ X D pos i).symm k.1).1, ((posJ X D pos i).symm k.1).2, (Fin.cast h.symm k.2.1, Fin.cast h.symm k.2.2)⟩

theorem valZ_rename_frVar (i : ℕ) {n : ℕ} (h : (X.Pj i).m + 1 = n) (R0 : MvPolynomial (GL3Theta.FrV D n) ℂ)
    (f : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) :
    valZ X D pos i h (MvPolynomial.rename (frVarToModel X D pos i h) R0) f = GL3Theta.evFr D R0 (zT X D pos f) := by
  unfold valZ GL3Theta.evFr
  rw [MvPolynomial.eval_rename]
  congr 2
  funext k
  simp [frVarToModel]

end GlobalTheory.TwV.DelA
end

noncomputable section
namespace GlobalTheory.TwV.DelA

theorem realises_of_wtPol : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) {n : ℕ} (h : (X.Pj (j + 1)).m + 1 = n) (ν : D.what₂.Tau → Fin n → ℕ), (∀ τ r, (ν τ r : ℤ) ≤ cT1 X D pos j τ) → ∀ Q : MvPolynomial (GL3Theta.FrV D n) ℂ, Q ∈ WtPol ℂ ν → ∃ R, Realises X D pos (j + 1) h (wT X D pos j) Q R := by
  intro p _ X D pos j n h ν hν Q hQ
  obtain ⟨R0, hR0⟩ := GlobalTheory.T.weightPolynomial_div_detPow_eq_poly_of_blockMatrices X D pos ν (cT1 X D pos j) hν Q hQ
  refine ⟨(∏ τ, if IsOddPos (pos.symm τ).2 then sgRev n ^ (-(wT X D pos j τ - cT1 X D pos j τ)) else 1) •
    MvPolynomial.rename (frVarToModel X D pos (j + 1) h) R0, ?_⟩
  intro f
  have hd : ∀ τ, (f.1 τ).det ≠ 0 := fun τ => (f.2 τ).ne_zero
  have hv := valZ_rename_frVar X D pos (j + 1) h R0 f.1
  unfold valZ at hv
  rw [ev1_eq_prod_det_pow_mul_valZ]
  unfold valZ
  rw [MvPolynomial.smul_eval, hv, hR0 f.1 hd]
  have key : (∏ τ, (zT X D pos f.1 τ).det ^ eT X D pos (j + 1) τ) *
      (∏ τ, if IsOddPos (pos.symm τ).2 then sgRev n ^ (-(wT X D pos j τ - cT1 X D pos j τ)) else 1) *
      (∏ τ, if IsOddPos (pos.symm τ).2 then (f.1 τ).det ^ (-(cT1 X D pos j τ)) else 1) =
      ∏ τ, (f.1 τ).det ^ (-(wT X D pos j τ)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [(GlobalTheory.T.realPlaceBlockWeightLastEntry_consecutive_levels X D pos j τ).2]
    by_cases ho : IsOddPos (pos.symm τ).2
    · simp only [if_pos ho]
      rw [det_zT_of_odd X D pos f.1 τ ho, mul_zpow, inv_zpow']
      have hs : sgRev n ^ (wT X D pos j τ - cT1 X D pos j τ) * sgRev n ^ (-(wT X D pos j τ - cT1 X D pos j τ)) = 1 := by
        rw [← zpow_add₀ (sgRev_ne_zero_of_sq n), add_neg_cancel, zpow_zero]
      have hdd : (f.1 τ).det ^ (-(wT X D pos j τ - cT1 X D pos j τ)) * (f.1 τ).det ^ (-(cT1 X D pos j τ)) =
          (f.1 τ).det ^ (-(wT X D pos j τ)) := by
        rw [← zpow_add₀ (hd τ)]; congr 1; ring
      calc _ = (sgRev n ^ (wT X D pos j τ - cT1 X D pos j τ) * sgRev n ^ (-(wT X D pos j τ - cT1 X D pos j τ))) *
            ((f.1 τ).det ^ (-(wT X D pos j τ - cT1 X D pos j τ)) * (f.1 τ).det ^ (-(cT1 X D pos j τ))) := by ring
        _ = _ := by rw [hs, hdd, one_mul]
    · simp only [if_neg ho, mul_one]
      rw [det_zT_of_even X D pos f.1 τ ho]
  rw [← key]
  ring

end GlobalTheory.TwV.DelA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeDetIdealCharacterEqConstMulDet
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.Xc.DetIdChi

open Matrix

theorem heq_transport (D : D7) {n N : ℕ} (h : n = N) (K : Submodule (𝓞 D.host.E) (Fin n → D.host.E))
    (K' : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (hK : HEq K K') :
    (IsSDLat D.host.E n K → IsSDLat D.host.E N K') ∧ TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) K = TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) K' := by
  subst h
  cases eq_of_heq hK
  exact ⟨id, rfl⟩

def coGL {E : Type} [Field E] {N : ℕ} (f : (Fin N → E) ≃ₗ[E] (Fin N → E)) : GL (Fin N) E :=
  ⟨LinearMap.toMatrix' (f : (Fin N → E) →ₗ[E] (Fin N → E)), LinearMap.toMatrix' ((f.symm : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)),
    by rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id],
    by rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]⟩

theorem toLE_coGL {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (f : (Fin N → E) ≃ₗ[E] (Fin N → E)) : toLE (coGL f) = f := by
  refine LinearEquiv.ext fun x => ?_
  rw [toLE_apply]
  show LinearMap.toMatrix' (f : (Fin N → E) →ₗ[E] (Fin N → E)) *ᵥ x = f x
  rw [LinearMap.toMatrix'_mulVec]
  rfl

theorem inv_mul_mem_UJ {E : Type} [Field E] [StarRing E] (σ : E →+* E) (hσ : ∀ x, σ x = star x) {N : ℕ} (G : Matrix (Fin N) (Fin N) E)
    (crd co : GL (Fin N) E) (h1 : cT σ crd.1 * crd.1 = G) (h2 : star co.1 * co.1 = G) : crd⁻¹ * co ∈ UJ σ G := by
  show cT σ ((crd⁻¹ * co : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * G * ((crd⁻¹ * co : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = G
  rw [← Emat.star_eq_cT σ hσ] at h1 ⊢
  rw [Units.val_mul, star_mul, ← h1]
  have e : star ((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * star (crd : Matrix (Fin N) (Fin N) E) = 1 := by
    rw [← star_mul, Units.mul_inv, star_one]
  have e' : (crd : Matrix (Fin N) (Fin N) E) * ((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) = 1 := Units.mul_inv crd
  calc star (co : Matrix (Fin N) (Fin N) E) * star ((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * (star (crd : Matrix (Fin N) (Fin N) E) * crd) *
        (((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * co)
      = star (co : Matrix (Fin N) (Fin N) E) * (star ((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * star (crd : Matrix (Fin N) (Fin N) E)) *
        ((crd : Matrix (Fin N) (Fin N) E) * ((crd⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)) * co := by
          simp only [Matrix.mul_assoc]
    _ = star (co : Matrix (Fin N) (Fin N) E) * co := by rw [e, e', Matrix.mul_one, Matrix.mul_one]
    _ = star (crd : Matrix (Fin N) (Fin N) E) * crd := by rw [h2, h1]

end GlobalTheory.TwV.Xc.DetIdChi

open GlobalTheory.TwV.Xc.DetIdChi in
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.TwV.Xc.chi_detId_kerN_eq : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m), ∃ c0 : ℂ, ∀ La : (sysS H X std).Lt j, ((sysS H X std).Pj j).IsLatTup La.2 → IsSDLat D.host.E _ ((J.fd std).kerN j La) → t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j La)) = c0 * chiI J ((J.fd std).dt j La)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hSpl j hj
  have hσ : ∀ x : D.host.E, (sigD D : D.host.E →+* D.host.E) x = star x := fun _ => rfl
  set G := gramN D j hj with hG
  set crd := J.A.crd j hj with hcrd
  have hco := (GlobalTheory.TwV.Xc.eMat_unitary_det D.host.E (sigD D : D.host.E →+* D.host.E) hσ (D.R.N j) (D.R.N j) rfl G crd
    (J.pins.crd_orth j hj)).1
  set co : GL (Fin (D.R.N j)) D.host.E := coGL (stdCo (sigD D : D.host.E →+* D.host.E) G) with hcoDef
  have hco2 : star co.1 * co.1 = G := Emat.gram_of_orth _ hσ G _ hco
  set γ₀ := crd⁻¹ * co with hγ₀
  have hγ : γ₀ ∈ UJ (sigD D : D.host.E →+* D.host.E) G := inv_mul_mem_UJ _ hσ G crd co (J.pins.crd_orth j hj) hco2
  have hr : GlobalTheory.TwU.ratA D.host.F γ₀ ∈ UPts (sigD D) G (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    Formalism.UG.P.rational_points_le_holds _ _ _ _ _ _ ⟨γ₀, hγ, rfl⟩
  have hch := GlobalTheory.T.charOnNormOneIdeles_mul_unramified_classValue S hDict hSpl
  refine ⟨chiI J (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀)), ?_⟩

  have key : ∀ (β : (J.St j hj).Ch) (x : UA D j hj), IsSDLat D.host.E _ (latK D.sp G J.a x.1 ((J.St j hj).K β).lev.Lb) →
      t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) (latK D.sp G J.a x.1 ((J.St j hj).K β).lev.Lb)) =
        chiI J (Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀)) * chiI J (Matrix.GeneralLinearGroup.det x.1) := by
    intro β x hsd
    let y : UA D j hj := ⟨GlobalTheory.TwU.ratA D.host.F γ₀ * x.1, mul_mem hr x.2⟩
    have hlat : latK D.sp G J.a x.1 ((J.St j hj).K β).lev.Lb = GlobalTheory.TwU.latCo D.sp G crd J.a y.1 ((J.St j hj).K β).lev.Lb := by
      rw [← GlobalTheory.TwU.latCo_eq_latK G co (toLE_coGL _), show co = crd * γ₀ by rw [hγ₀, mul_inv_cancel_left]]
      exact GlobalTheory.TwU.latCo_mul G crd γ₀ hγ J.a x.1 _
    obtain ⟨hg, hcar, d, hdd, hdet⟩ := GlobalTheory.T.stepCoords_conj_unitary_and_carries_companion J.A J.dtU J.a J.pins J.tie j hj β y
    rw [J.base j hj β] at hcar
    have hstd : IsSDLat D.host.E (D.R.N j) (StandardLatticesGL3.stdL D (D.R.N j)) := by
      have := ((t.O u μ).L0 j).2
      rwa [Formalism.L2.Ker.initial_lattice_eq_standard] at this
    rw [hlat] at hsd ⊢
    have hrel := J.rel (D.R.N j) ⟨_, hstd⟩ ⟨_, hsd⟩ _ hg hcar d hdet
    have hid := t.idl_ok.2.2.2.2 (D.R.N j) ⟨_, hstd⟩ ⟨_, hsd⟩
    rw [hrel] at hid
    have hx1 := GlobalTheory.TwV.det_unitary_adelic_point_gram_step_norm_one D j hj x
    have hy1 := GlobalTheory.TwV.det_unitary_adelic_point_gram_step_norm_one D j hj y
    have hr1 : Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀) ∈ U1 (sigD D) := by
      have e : Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀) =
          Matrix.GeneralLinearGroup.det y.1 * (Matrix.GeneralLinearGroup.det x.1)⁻¹ := by
        show _ = Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀ * x.1) * _
        rw [MonoidHom.map_mul Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀) x.1, mul_inv_cancel_right]
      rw [e]
      exact mul_mem hy1 (inv_mem hx1)
    rw [← hch.1 _ hr1 _ hx1, show Matrix.GeneralLinearGroup.det (GlobalTheory.TwU.ratA D.host.F γ₀) * Matrix.GeneralLinearGroup.det x.1 =
      Matrix.GeneralLinearGroup.det d.1 by rw [hdd]; exact (map_mul _ _ _).symm, hch.2.2.1 d]
    show t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D (D.R.N j)) (⟨_, hsd⟩ : SDLat D.host.E (D.R.N j)).1) = _
    rw [← hid, t.χ_rec, TaylorLogMetric.chiRec_idl D t.idl t.idl_ok.1]
    rfl
  intro La hLa hsd
  obtain ⟨⟨hr', -⟩, -, hheq, hdt⟩ := hDict j hj La hLa
  obtain ⟨h1, h2⟩ := heq_transport D hr' _ _ hheq
  rw [h2, hdt]
  exact key _ _ (h1 hsd)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeFirstFactorLatticeTuplePointStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelLatticeFirstFactor_latticeTuplePoint : ∀ {D : D7} {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) {p : ℕ} {G : GAtP p} (A : LocAt D.host.F D.host.E (D.R.N i) G) (a : 𝓞 D.host.E), (∃ co, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) co) → SplAlg A → LocInt A → LbAtB A lev.Lb → 0 < T → ∀ (c : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), A.IsPt c g x.1 → ∀ v, IsUnit (T : G.P.W v) → locSp (G.P.W v) (A.iw v) (latK D.sp (gramN D i hi) a x.1 lev.Lb) = colSpan (G.P.W v) ((LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi)).toLinearMap * A.B.1).map (A.iw v) * (castGL A.rk (G.P.Qq v) (g v) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) (G.P.Qq v))) := by
  first | exact @GlobalTheory.TwV.KerSp.locSp_latK_isPt | exact GlobalTheory.TwV.KerSp.locSp_latK_isPt | (intros; apply GlobalTheory.TwV.KerSp.locSp_latK_isPt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeMovedLatticeTupleStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelLattice_movedLatticeTuple : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j < D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ) (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj.le).K (J.chart std j hj.le (c, La))).lev.U) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j), ((sysS H X std).Pj j).IsLatTup La → MoveBy std J j hj.le c La γ g κ → (J.fd std).kerN j (c, (((sysS H X std).Lv.lev j c).smul γ La)) = SDLat.smulLat (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj.le) g) ((J.fd std).kerN j (c, La))) := by
  first | exact @GlobalTheory.TwV.Xc.kerN_smul | exact GlobalTheory.TwV.Xc.kerN_smul | (intros; apply GlobalTheory.TwV.Xc.kerN_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepAdelicDatumLevelEquivariance
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.TwTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem locAt : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (x x₁ : UA D (t.m2 + 1) (Nat.le_of_succ_le hi)) (x' x₁' : UA D (t.m2 + 1 + 1) hi)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' →
    ∀ (P : SB t μ) g z g' z', A.cplRel β P g z →
      InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 g →
      TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P g' z' →
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 g' →
    ∀ Z, z' * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z *
        rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g : t.X.Eˣ) : t.X.E) *
        rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g' : t.X.Eˣ) : t.X.E) =
      z * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P
  by_cases hP : P.1 ∈ t.Pr.vGs
  · exact GlobalTheory.T.lastStep_localFactor_levelValues_typePrime A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P hP
  · exact GlobalTheory.T.columnLastStep_localFactor_twist_prime_law A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P hP

end GlobalTheory.TwTop

namespace GlobalTheory.TwTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem levAt_top : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU →
    ∀ i hi, i = t.m2 + 1 → PtAway A a i hi → LevAt A dtU a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hEx hMu i hi hieq _hAway
  subst hieq
  intro β β' x x' x₁ x₁' κ κ' hx hx' z
  have key : ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' → ∀ Z,
      muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St (t.m2 + 1) _).K β).lev.chi κ : ℂˣ) : ℂ) *
          t.seam.σ₀ (xiPt A (t.m2 + 1) hi β β' p₁ p₁' Z) =
        muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (t.m2 + 1 + 1) hi).K β').lev.chi κ' : ℂˣ) : ℂ) *
          t.seam.σ₀ (xiPt A (t.m2 + 1) hi β β' p p' Z) := by
    intro p p' p₁ p₁' hp hp' hp₁ hp₁' Z
    have hxi : ∀ q q', xiPt A (t.m2 + 1) hi β β' q q' Z =
        _root_.Formalism.L2.Col.XiTop t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) q (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β q) q' Z := by
      intro q q'
      unfold xiPt
      rw [dif_neg (by omega), if_neg (by omega)]
    have e1 := hxi p₁ p₁'
    have e2 := hxi p p'
    have e3 := GlobalTheory.T.chartDatum_levelPrime_invariant_mul_level A dtU a hPin hTie (t.m2 + 1) hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' Z
    simp only [e1, e2, xiTop_eq_prod, e3]
    have hC := hTie.levCpl β
    have hT2 := hTie.levTop β'
    have hLe := hC.1
    have hChi := hC.2.2
    have hLe' := hT2.1
    have hChi' := hT2.2
    have hU := (((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U_eq κ.1).1 κ.2
    have hU' := (((St (t.m2 + 1 + 1) hi).K β').lev.U_eq κ'.1).1 κ'.2
    have hov : ∀ P : SB t μ, IsOver (HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P.1)) (seamP t.seam P.1) := by
      intro P
      unfold IsOver
      rw [HeightOneSpectrum.under_asIdeal]
    choose g zz hg using fun P : SB t μ => hLe P _ (hov P) κ.1 hU.1 (hU.2 _)
    choose g' zz' hg' using fun P : SB t μ => hLe' P _ (hov P) κ'.1 hU'.1 (hU'.2 _)
    have c1 := hChi κ g zz hg
    have c2 := hChi' κ' g' zz' hg'
    have hm := GlobalTheory.T.lastStepCharacter_at_levelDet_mul_localCharacters A dtU a hPin hTie hMu hi β β' κ κ' g zz g' zz' hg hg'
    have hprod : (∏ P, zz' P) * (∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁
          (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z) *
        (∏ P, rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E) *
          rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g' P) : t.X.Eˣ) : t.X.E)) =
        (∏ P, zz P) * ∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p
          (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun P _ => ?_
      rw [← locAt A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P (g P) (zz P) (g' P) (zz' P)
        (hg P).1 (hg P).2 (hg' P).1 (hg' P).2 Z]
      ring
    have e := congrArg t.seam.σ₀ hprod
    simp only [map_mul] at e ⊢
    have hA : t.seam.σ₀ (∏ P, zz P) ≠ 0 := right_ne_zero_of_mul_eq_one c1
    have hB : t.seam.σ₀ (∏ P, zz' P) ≠ 0 := right_ne_zero_of_mul_eq_one c2
    apply mul_right_cancel₀ (mul_ne_zero hA hB)
    linear_combination
      (-(((((St (t.m2 + 1) _).K β).lev.chi κ : ℂˣ) : ℂ) * t.seam.σ₀ (phiT t.X.K p.deco.1 p'.deco.1 Z) *
        t.seam.σ₀ (∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z) *
        t.seam.σ₀ (∏ P, zz P) * t.seam.σ₀ (∏ P, zz' P))) * hm +
      (muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (phiT t.X.K p.deco.1 p'.deco.1 Z) *
        t.seam.σ₀ (∏ P, zz' P) *
        t.seam.σ₀ (∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z) *
        t.seam.σ₀ (∏ P, rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E) *
          rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g' P) : t.X.Eˣ) : t.X.E))) * c1 +
      (muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (phiT t.X.K p.deco.1 p'.deco.1 Z)) * e -
      (muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (phiT t.X.K p.deco.1 p'.deco.1 Z) *
        t.seam.σ₀ (∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) *
        t.seam.σ₀ (∏ P, zz P)) * c2
  have h₁ : (∃ p, IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p) ∧ ∃ p', IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p' :=
    ⟨hEx _ _ β x₁, hEx _ _ β' x₁'⟩
  have h₀ : (∃ p, IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' :=
    ⟨hEx _ _ β x, hEx _ _ β' x'⟩
  unfold xiAd
  rw [dif_pos h₁, dif_pos h₀]
  exact key _ _ _ _ h₀.1.choose_spec h₀.2.choose_spec h₁.1.choose_spec h₁.2.choose_spec _

end GlobalTheory.TwTop

end
end

