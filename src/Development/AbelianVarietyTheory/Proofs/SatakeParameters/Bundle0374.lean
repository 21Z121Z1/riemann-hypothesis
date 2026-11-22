import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0372
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0369
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0373
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0367
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0362
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0009
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0347
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0350
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0349
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0363
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0348
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0032
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsGHeckeMapForget
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicDatumLevelEquivarianceFirstCoupledStep
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.AdLevCpl

open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in
set_option maxHeartbeats 2000000 in
theorem levAt_coupled : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i = t.m2 → PtAway A a i hi → LevAt A dtU a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie hEx hMu i hi hi2 hAw
  have key : ∀ β β' x x' p p', IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' → ∀ z,
      xiAd A a i hi β β' x x' z = t.seam.σ₀ (xiPt A i hi β β' p p' (seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))) := by
    intro β β' x x' p p' hp hp' z
    have hh : (∃ p, IsPtAd A a i (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (i + 1) hi β' x' p' := ⟨⟨p, hp⟩, ⟨p', hp'⟩⟩
    unfold xiAd
    rw [dif_pos hh]
    rw [hAw β β' x x' x x' p p' hh.1.choose hh.2.choose hp hp' hh.1.choose_spec hh.2.choose_spec (fun v _ => ⟨rfl, rfl⟩)]
  intro β β' x x' x₁ x₁' κ κ' h1 h1' z
  obtain ⟨p, hp⟩ := hEx i (Nat.le_of_succ_le hi) β x
  obtain ⟨p', hp'⟩ := hEx (i + 1) hi β' x'
  obtain ⟨p₁, hp₁⟩ := hEx i (Nat.le_of_succ_le hi) β x₁
  obtain ⟨p₁', hp₁'⟩ := hEx (i + 1) hi β' x₁'
  rw [key β β' x₁ x₁' p₁ p₁' hp₁ hp₁' z, key β β' x x' p p' hp hp' z]
  have hs := GlobalTheory.T.firstCoupledStep_adelicDatum_source_level_law A dtU a hP hTie hEx hMu i hi hi2 hAw β β' x x₁ x₁' κ p p₁' p₁ h1 hp hp₁' hp₁ (seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))
  have ht := GlobalTheory.T.firstCoupledStep_adelicDatum_law_targetLevel A dtU a hP hTie hEx hMu i hi hi2 hAw β β' x x' x₁' κ' p p' p₁' h1' hp hp' hp₁' (seamHom t.seam (inFr
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i (Nat.le_of_succ_le hi)) (A.crd i (Nat.le_of_succ_le hi)))
        (toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (i + 1) hi) (A.crd (i + 1) hi)) z))
  linear_combination (muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ'.1)) * hs +
    (muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1)) * ht

end GlobalTheory.AdLevCpl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChangedFrameRationalUnitaryStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.changedFrame_rational_unitary : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j), StdU D (mM d j hj La) ∧ FrIs d.fd2 (J.rho std) j La h (mM d j hj La) ∧ (mM d j hj La).1.det * (d.gam j hj La).1.det = (uB J j hj La.1).1.det) := by
  first | exact @GlobalTheory.TwV.DelA.changed_frame_unitary | exact GlobalTheory.TwV.DelA.changed_frame_unitary | (intros; apply GlobalTheory.TwV.DelA.changed_frame_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointsExistAndClassPointsRepresentativesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartPoints_exist_and_classPoints_representatives : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a ∧ ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c)) := by
  first | exact @GlobalTheory.TwV.ptEx_isPtAd | exact GlobalTheory.TwV.ptEx_isPtAd | (intros; apply GlobalTheory.TwV.ptEx_isPtAd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComparedFormNormalisedValuesLatticeTuple
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 800000 in

theorem GlobalTheory.TwV.DelA.cmp_valsAt : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) j (hj : j + 1 ≤ D.R.m) (h : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ x : ((ex.tw.fm u μ).lat (j + 1)).V, ∃ V : XR ((sysS H X std).Pj (j + 1)) ℂ, MvPolynomial.map (algebraMap (sysS H X std).G.Kf ℂ_[D.what₂.places.resChar w]) ((kaAt X H hT).cmp (j + 1) x La.1 La.2) = MvPolynomial.map ι V ∧ RealAt d (j + 1) hj h La ((ex.tw.fm u μ).emb (j + 1) x) V) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hDict hPos ι hι
  letI := wittFractionAlgebraCp (D.what₂.places.resChar w)
  letI := algKfC S.E.toCEmb
  intro d j hj h La hLa x
  have hr := (GlobalTheory.TwV.DelA.posTie_at S hPos ι hι).2
  obtain ⟨c, κ, _, hκ, hy, hiff⟩ := GlobalTheory.T.realAt_succ_iff_decomposition_values S d j hj h La hLa
  obtain ⟨g, hgb, hpt⟩ := GlobalTheory.T.latticeTupleSuccLevel_point_isComponentPointInChart S hDict j hj La hLa
  have hH := ((H.core j hj) ((I.at' j hj).st.eC.symm La.1).1).toHyp Formalism.L2.G.RelativeIndexFlags.blockRationality_holds
  have hv := valC_spec hH.ex ((I.at' j hj).eps.symm x) ((I.at' j hj).st.eC.symm La.1).2 La.2 hLa
  refine ⟨MvPolynomial.map D.what₂.embLL (valC ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev (embT D) D.what₂.embLL
    ((I.at' j hj).st.charts.gat ((I.at' j hj).st.eC.symm La.1).1) ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1)
    (I.at' j hj).st.pos ((I.at' j hj).st.embN ((I.at' j hj).st.eC.symm La.1).1) ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y
    ((I.at' j hj).eps.symm x) ((I.at' j hj).st.eC.symm La.1).2 La.2), ?_, ?_⟩
  · rw [kaAt_cmp X H hT j hj x]
    show MvPolynomial.map _ (cmpC _ _ _ _ _ _ _ _ _ _ _ _) = _
    simp only [cmpC, hLa, if_true]
    rw [MvPolynomial.map_map, MvPolynomial.map_map]
    refine congrArg (fun f => MvPolynomial.map f _) ?_
    exact RingHom.ext fun r => (hr r).symm
  · rw [hiff]
    intro z z' hz
    have h2 : trC (X.onCh j hj) (j + 1) ((ex.tw.fm u μ).emb (j + 1) x) =
        (I.at' j hj).M.emb (j + 1) ((I.at' j hj).eps.symm x) := by
      apply trC_heq
      have := (I.at' j hj).eps_emb ((I.at' j hj).eps.symm x)
      rwa [LinearEquiv.apply_symm_apply] at this
    have hp1 := hpt
    rw [d.eq (j + 1) hj La hLa, hy] at hp1
    have hk := congrArg (fun k => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).IsPt ((I.at' j hj).st.eC.symm La.1).2 g
      (GlobalTheory.TwU.ratA D.host.F (d.gam (j + 1) hj La) * (((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).y c).1 * k)) hκ
    have hp2 := hk.mpr hp1
    have hv2 := hv.2 g hgb c (d.gam (j + 1) hj La) (d.mem (j + 1) hj La) κ hp2 z z' hz
    rw [h2, ← embN_eq_nrmR]
    exact hv2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComplexBlockActionInvReadAsSubstitutionStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_block_action_inv_read_as_substitution : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (j : ℕ) (hN : RankTie X D j) (La' : X.Lt (j + 1)) (M : GL (Fin (D.R.N (j + 1))) D.host.E), StdU D M → FrIs fd ρ (j + 1) La' (rkT X D hN) M → ∀ R : XR (X.Pj (j + 1)) ℂ, MvPolynomial.map ι (actC X D pos (j + 1) (rkT X D hN) M⁻¹ R) = ι (∏ τ, embT D τ (M : Matrix (Fin (D.R.N (j + 1))) (Fin (D.R.N (j + 1))) D.host.E).det ^ (if IsOddPos (pos.symm τ).2 then cT1 X D pos j τ - wT X D pos j τ else -wT X D pos j τ)) • GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.mk Kc fd j La') (MvPolynomial.map ι R) := by
  first | exact @GlobalTheory.TwV.DelA.actC_inv_read | exact GlobalTheory.TwV.DelA.actC_inv_read | (intros; apply GlobalTheory.TwV.DelA.actC_inv_read <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetLatticeTuplesAgreeingAwayFromPlaceStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_latticeTuples_agreeing_away_from_place : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ v π, IsUnifAt J v π → ∀ j (hj : j ≤ D.R.m) (La Lb : (sysS H X std).Lt j), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → ∃ k ∈ U1 (sigD D), k ∈ intU D.host.F D.host.E ∧ OneOff ((A0 J).pl v).1 k ∧ (J.fd std).dt j La = (J.fd std).dt j Lb * π ^ (len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2) * k) := by
  first | exact @GlobalTheory.TwV.Xc.dt_sameAway_step | exact GlobalTheory.TwV.Xc.dt_sameAway_step | (intros; apply GlobalTheory.TwV.Xc.dt_sameAway_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EvenFrameBlockScalingHomogeneousPolynomial
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.FrameB.evenFrameBlock_scaling_homogeneous_polynomial : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (fd : FData X D) (c : Kc) (j : ℕ) (La' : X.Lt (j + 1)) (d : D.what₂.Tau → ℤ) (R : XspC (X.Pj (j + 1)) Kc), (∀ m ∈ R.support, ∀ τ, ¬ IsOddPos (pos.symm τ).2 → (∑ x : Var (X.Pj (j + 1)), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj (j + 1)).nV, Fin ((X.Pj (j + 1)).n' v)) = (posJ X D pos (j + 1)).symm τ then (m x : ℤ) else 0) = d τ) → GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') R = (∏ τ, if IsOddPos (pos.symm τ).2 then 1 else c ^ d τ) • GlobalTheory.FrameB.tau0 X Kc j (GlobalTheory.FrameB.mk Kc fd j La') R := by
  intro p _ X D pos Kc _ _ _ fd c j La' d R hR
  classical
  let blk : Var (X.Pj (j + 1)) → Σ v : Fin (X.Pj (j + 1)).nV, Fin ((X.Pj (j + 1)).n' v) := fun y => ⟨y.1, y.2.1⟩
  let E : (Σ v : Fin (X.Pj (j + 1)).nV, Fin ((X.Pj (j + 1)).n' v)) → Kc := fun b => if IsOddPos b.2 then 1 else c
  have hf : ∀ y, GlobalTheory.FrameB.frF X Kc j (GlobalTheory.FrameB.wV Kc fd c j La') y =
      MvPolynomial.C (E (blk y)) * GlobalTheory.FrameB.frF X Kc j (GlobalTheory.FrameB.mk Kc fd j La') y := by
    intro y
    unfold GlobalTheory.FrameB.frF GlobalTheory.FrameB.wV
    simp only [E, blk]
    split_ifs with h1 h2 h2
    · simp only [MvPolynomial.C_1, one_mul]
    · exact absurd h1 h2
    · exact absurd h2 h1
    · simp only [Matrix.smul_apply, smul_eq_mul, MvPolynomial.C_mul, Finset.mul_sum, mul_assoc]
  have hm : ∀ m ∈ R.support, (∏ y, E (blk y) ^ m y) = ∏ τ, if IsOddPos (pos.symm τ).2 then 1 else c ^ d τ := by
    intro m hmR
    rw [← Finset.prod_fiberwise Finset.univ blk, ← (posJ X D pos (j + 1)).prod_comp]
    refine Finset.prod_congr rfl fun b _ => ?_
    have hpb : pos.symm (posJ X D pos (j + 1) b) = b := pos.symm_apply_apply b
    have h2 : ∏ y ∈ Finset.univ.filter (fun y => blk y = b), E (blk y) ^ m y =
        E b ^ (∑ y ∈ Finset.univ.filter (fun y => blk y = b), m y) := by
      rw [← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_congr rfl fun y hy => ?_
      rw [(Finset.mem_filter.1 hy).2]
    rw [h2, hpb]
    simp only [E]
    split_ifs with h1 h3 h3
    · exact one_pow _
    · exact absurd h1 h3
    · exact absurd h3 h1
    · have hd := hR m hmR (posJ X D pos (j + 1) b) (by rw [hpb]; exact h1)
      rw [Equiv.symm_apply_apply, ← Finset.sum_filter] at hd
      rw [← hd, ← Nat.cast_sum, zpow_natCast]
  unfold GlobalTheory.FrameB.tau0
  conv_lhs => rw [R.as_sum]
  conv_rhs => rw [R.as_sum]
  simp only [map_sum, Finset.smul_sum, MvPolynomial.aeval_monomial]
  refine Finset.sum_congr rfl fun m hmR => ?_
  rw [← hm m hmR]
  simp only [hf]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, Algebra.smul_def, MvPolynomial.algebraMap_eq]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrameLocalLatticeSpanKernelLatticeSuccStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_localLattice_span_kernelLattice_succ : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ j, j + 1 ≤ D.R.m → ∀ La : (sysS H X std).Lt (j + 1), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN (j + 1) La) = ((sysS H X std).latAt v (j + 1) La.2).map ((((J.fd std).frM (j + 1) La v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
  first | exact @GlobalTheory.TwV.Joint.locSp_kerN_succ | exact GlobalTheory.TwV.Joint.locSp_kerN_succ | (intros; apply GlobalTheory.TwV.Joint.locSp_kerN_succ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrameLocalLatticeSpanKernelLatticeZeroStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_localLattice_span_kernelLattice_zero : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ La : (sysS H X std).Lt 0, ((sysS H X std).Pj 0).IsLatTup La.2 → ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN 0 La) = ((sysS H X std).latAt v 0 La.2).map ((((J.fd std).frM 0 La v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
  first | exact @GlobalTheory.TwV.Joint.locSp_kerN_zero | exact GlobalTheory.TwV.Joint.locSp_kerN_zero | (intros; apply GlobalTheory.TwV.Joint.locSp_kerN_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckePowOne
section
noncomputable section

namespace GlobalTheory.WeightTwoHeckePower

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G R} {N M : ℕ}

abbrev sPow (X : GenModel gb N) (r : ℕ) : (GlobalTheory.KS.pow X.univ.A r).left ⟶ Sp R :=
  (GlobalTheory.KS.pow X.univ.A r).hom ≫ X.s

theorem liftMap_w {X : GenModel gb N} {X' : GenModel gb M} {f : X'.X ⟶ X.X} {o : GObj gb N X'.s}
    (ψ : X'.univ.A ⟶ o.A) (m : GObjMap o X.univ f) :
    (ψ.left ≫ m.φ) ≫ X.univ.A.hom = X'.univ.A.hom ≫ f := by
  rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w]

def liftPow {X : GenModel gb N} {X' : GenModel gb M} {f : X'.X ⟶ X.X} {o : GObj gb N X'.s}
    (ψ : X'.univ.A ⟶ o.A) (m : GObjMap o X.univ f) (r : ℕ) :
    (GlobalTheory.KS.pow X'.univ.A r).left ⟶ (GlobalTheory.KS.pow X.univ.A r).left :=
  GlobalTheory.KS.powMap f (ψ.left ≫ m.φ) (liftMap_w ψ m) r

def actPow {S : Scheme.{0}} (A : Over S) [GrpObj A] (act : OActN G.O A) (α : G.O) (r : ℕ) :
    (GlobalTheory.KS.pow A r).left ⟶ (GlobalTheory.KS.pow A r).left :=
  (Limits.Pi.map fun _ : Fin r => act.act α).left

def heckePow {X : GenModel gb N} {X' : GenModel gb M} {f : X'.X ⟶ X.X} {o : GObj gb N X'.s}
    (ψ : X'.univ.A ⟶ o.A) (m : GObjMap o X.univ f) (α : G.O) (r : ℕ) :
    (GlobalTheory.KS.pow X'.univ.A r).left ⟶ (GlobalTheory.KS.pow X.univ.A r).left :=
  liftPow ψ m r ≫ actPow X.univ.A X.univ.act α r

end GlobalTheory.WeightTwoHeckePower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointsAtSplitUnramifiedPlacesOfChainChartsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jointsAtSplitUnramifiedPlaces_of_chainCharts : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (μ : D.what₂.Tup), G.LatTied hT Gi Gl → (∀ u, Nonempty (JIn t u μ)) → GlobalTheory.TwV.JointsAt t μ := by
  first | exact @GlobalTheory.TwV.jointsAt_of_jIn | exact GlobalTheory.TwV.jointsAt_of_jIn | (intros; apply GlobalTheory.TwV.jointsAt_of_jIn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelScalarOfSourceTargetPartsProductStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelScalar_of_sourceTarget_parts_product : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std) (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]), ∀ j < D.R.m, ∀ (cB : ∀ j, (sysS H X std).Lt j → ℂ_[D.what₂.places.resChar w]) (sc : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → ℂ_[D.what₂.places.resChar w]) (cK : ℂ_[D.what₂.places.resChar w]), (∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → cK * cB j La * ι (d.uS S j La) * ι (d.uT S j La') = sc j La'.1 La'.2) → TieChiH S.Y t u μ (clsAt X H) (fun j => clsAt X H (j + 1)) ι sc (d.sH S ι) cB j cK) := by
  first | exact @GlobalTheory.TwV.DelB.tieChiH_of_parts | exact GlobalTheory.TwV.DelB.tieChiH_of_parts | (intros; apply GlobalTheory.TwV.DelB.tieChiH_of_parts <;> assumption)
end

