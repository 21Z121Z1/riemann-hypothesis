import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0358
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.PNeatB
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0283
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0324
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0361
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0362
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0032
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0290
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0360
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChiFinOfGlevH
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BaseLatticeSelfDualOfLocalEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0345
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0342
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0343
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0359
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0293
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0294
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0363
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0002
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0344
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0349
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0348
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0108

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChangedFrameEqCoordMulInvMulBasis
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.DelB

section SlopeTestRemainingChoices
variable {E : Type} [Field E]
theorem toMatrix'_stdCo_reindex {n N : ℕ} (h : N = n) (σ : E →+* E) (G : Matrix (Fin N) (Fin N) E) :
    LinearMap.toMatrix' (stdCo σ (G.reindex (finCongr h) (finCongr h))).toLinearMap =
      (LinearMap.toMatrix' (stdCo σ G).toLinearMap).submatrix (Fin.cast h.symm) (Fin.cast h.symm) := by
  subst h
  simp

theorem toMatrix'_linEquiv_symm_mul {n : ℕ} (e : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    LinearMap.toMatrix' e.symm.toLinearMap * LinearMap.toMatrix' e.toLinearMap = 1 := by
  rw [← LinearMap.toMatrix'_comp]
  simp

theorem toMatrix'_toLE_eq {n : ℕ} (g : GL (Fin n) E) : LinearMap.toMatrix' (toLE g).toLinearMap = (g : Matrix (Fin n) (Fin n) E) := by
  simp only [toLE, LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap]
  exact LinearMap.toMatrix'_toLin' (g : Matrix (Fin n) (Fin n) E)

theorem toMatrix'_toLE_symm_eq {n : ℕ} (g : GL (Fin n) E) :
    LinearMap.toMatrix' (toLE g).symm.toLinearMap = ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
  rw [Matrix.coe_units_inv, ← toMatrix'_toLE_eq]
  exact (Matrix.inv_eq_left_inv (toMatrix'_linEquiv_symm_mul _)).symm
end SlopeTestRemainingChoices

section Site
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I}
  [Fact (D.what₂.places.resChar w).Prime] {t : KerEntTied ex} (J : Joint t H X) (std : Lt.StdAtW D Gl u w hg)

theorem Joint.cp_iw_eq_rho (j : ℕ) (La : (sysS H X std).Lt j) (v : (sysS H X std).Pl) : (J.cp std).iw j La v = J.rho std v := by
  cases j with
  | zero => rfl
  | succ i =>
    simp only [Joint.cp, cpAt, chAt]
    split_ifs with hi
    · exact J.iw i hi _ v
    · rfl

theorem Joint.stdCo_cpJ_mat (j : ℕ) (hj : j ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j) :
    LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) ((J.cp std).J j La)).toLinearMap =
      (LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj)).toLinearMap).submatrix (Fin.cast hr) (Fin.cast hr) := by
  cases j with
  | zero =>
    simp only [Joint.cp, cpAt, chAt]
    exact toMatrix'_stdCo_reindex _ _ _
  | succ i =>
    simp only [Joint.cp, cpAt, chAt, dif_pos hj]
    exact toMatrix'_stdCo_reindex _ _ _

theorem gMat_eq_mul (j : ℕ) (hj : j ≤ D.R.m) (γ : GL (Fin (D.R.N j)) D.host.E) :
    gMat J j hj γ = LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj)).toLinearMap *
      ((γ : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) * (((J.A.crd j hj)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E)) := by
  unfold gMat toStdCo stdG
  simp only [LinearEquiv.coe_trans, LinearMap.toMatrix'_comp]
  rw [toMatrix'_toLE_eq, toMatrix'_toLE_symm_eq, mul_assoc (_ * _), ← mul_assoc (LinearMap.toMatrix' _), toMatrix'_linEquiv_symm_mul, one_mul,
    mul_assoc]
end Site

theorem changedFrame_eq_coord_mul_inv_mul_basis : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) La v, d.fd2.frM j La v = (((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E).submatrix (Fin.cast hr) (Fin.cast hr) * ((J.cp std).B j La).1.submatrix (Fin.cast ((J.cp std).hk j La)) (Fin.cast ((J.cp std).hk j La))).map (J.rho std v)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j hj hr La v
  have hU' : star (d.eM j La) * d.eM j La = 1 := mul_eq_one_comm.mp (GlobalTheory.T.decomposition_unitary_mul_star_eq_one S d j La)
  have hE : d.eM j La = (LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj)).toLinearMap *
      (((d.gam j hj La : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) *
        (((J.A.crd j hj)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E))).submatrix
        (finCongr hr) (finCongr hr) := by
    rw [Dec.eM, dif_pos ⟨hj, hr⟩, gMat_eq_mul]
    rfl
  have hC : LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) ((J.cp std).J j La)).toLinearMap =
      d.eM j La * (((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E).submatrix
        (finCongr hr) (finCongr hr)) := by
    rw [Joint.stdCo_cpJ_mat J std j hj hr La, hE, Matrix.submatrix_mul_equiv]
    have h1 : LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj)).toLinearMap *
        (((d.gam j hj La : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E) *
          (((J.A.crd j hj)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E)) *
        (((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E)) =
        LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj)).toLinearMap := by
      rw [Units.val_mul, mul_assoc, mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv, mul_one]
    rw [h1]
    rfl
  show (star (d.eM j La)).map (J.rho std v) * ((((LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) ((J.cp std).J j La)).toLinearMap) *
      ((J.cp std).B j La).1).map ((J.cp std).iw j La v)).submatrix (finCongr ((J.cp std).hk j La)) (finCongr ((J.cp std).hk j La))) = _
  rw [Joint.cp_iw_eq_rho, hC]
  change (star (d.eM j La)).map (J.rho std v) * (d.eM j La * (((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) :
      Matrix _ _ D.host.E).submatrix (Fin.cast hr) (Fin.cast hr)) * (show Matrix (Fin (((sysS H X std).Pj j).m + 1)) (Fin (((sysS H X std).Pj j).m + 1)) D.host.E from ((J.cp std).B j La).1)).map (J.rho std v) =
    ((((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) :
      Matrix _ _ D.host.E).submatrix (Fin.cast hr) (Fin.cast hr)) * (show Matrix (Fin (((sysS H X std).Pj j).m + 1)) (Fin (((sysS H X std).Pj j).m + 1)) D.host.E from ((J.cp std).B j La).1)).map (J.rho std v)
  rw [← Matrix.map_mul, ← mul_assoc, ← mul_assoc, hU', one_mul]

end GlobalTheory.TwV.DelB

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBasePointRightTranslateByChartLevel
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Hat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem levU_mulVec_mem_hatL (S : StepLevel F E σ J T f bad) (g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hg : g ∈ S.U)
    (z : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) (hz : z ∈ Formalism.L2.Herm.hatL (F := F) S.Lb) :
    (g : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z ∈ Formalism.L2.Herm.hatL (F := F) S.Lb := by
  refine Formalism.L2.Geo.Def.PN.latS_of_loc S.Lb S.Lb_span _ fun v => ?_
  have h1 := Formalism.L2.Geo.Def.PN.prV_latS S.Lb v hz
  have h2 : bc (prV (E := E) v) g ∈ levelVL σ J v S.Lb := S.Uloc_lev v (((S.U_eq g).1 hg).2 v)
  have h3 := (h2.2 _).1 h1
  have e : (fun i => prV (E := E) v (((g : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) *ᵥ z) i)) =
      ((bc (prV (E := E) v) g : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
        fun i => prV (E := E) v (z i) := by
    funext i
    exact RingHom.map_mulVec (prV (E := E) v) (g : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) z i
  rw [e]
  exact h3

theorem hatStab_of_levU (S : StepLevel F E σ J T f bad) (κ : S.U) : HatStab S.Lb κ.1 := by
  intro z
  constructor
  · intro hz
    have := levU_mulVec_mem_hatL S κ.1 κ.2 _ hz
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at this
  · intro hz
    exact levU_mulVec_mem_hatL S κ.1⁻¹ (S.U.inv_mem κ.2) z hz

end Hat

theorem isPtAd_mul_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p (κ : ((St i hi).K β).lev.U), x'.1 = x.1 * κ.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p') := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP H i hi β x x' p κ hx hp
  obtain ⟨p', hN, hf, hfr⟩ := GlobalTheory.T.chartPoint_frames_move_integralRightTranslate A dtU a hP H i p
    (fun P => ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P))
    (fun P => (ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P))
    (GlobalTheory.T.chartLevel_baseFrame_congr_one_at_badPrime A dtU a hP H i hi β x p κ hp) hp.frame
  refine ⟨p', ⟨?_, ?_, ?_⟩⟩
  · rw [hN, hp.lat]
    unfold latCo
    rw [hx, latAd_stab _ _ _ (hatStab_of_levU _ κ)]
  · intro P
    have e : ratA D.host.F (A.crd i hi) * x'.1 * ratA D.host.F (A.fb i hi β P) =
        ratA D.host.F (A.crd i hi) * x.1 * ratA D.host.F (A.fb i hi β P) *
          ((ratA D.host.F (A.fb i hi β P))⁻¹ * κ.1 * ratA D.host.F (A.fb i hi β P)) := by
      rw [hx]; simp only [mul_assoc, mul_inv_cancel_left]
    rw [e]
    exact hfr P
  · intro P v h hv
    have e : ratA D.host.F (A.crd i hi) * x'.1 = ratA D.host.F (A.crd i hi) * x.1 * κ.1 := by
      rw [hx, mul_assoc]
    have h1 := GlobalTheory.T.functionalCondition_invariant_rightLevelTranslate t.seam _ P v h (iotaOf A i hi β P v h) _ κ _ (hp.fnl P v h hv)
    rw [e]
    intro w hw z hz
    have h2 := h1 w (by rw [← hN]; exact hw) z hz
    exact (congrFun (congrFun hf P) w).trans h2

end GlobalTheory.TwV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnTupleStepZeroReadByMemberLevelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnTuple_stepZero_read_by_memberLevel : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch0 : ℕ → Type} {chOf0 : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch0 i} (F : FormsTiedSym (I.rec7 l Z) u Ch0 chOf0) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))), (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.StdF l Z u F → ∃ K0 : Fam I l Z u a 0 (Nat.zero_le _) (badQ (I.rec7 l Z) Q) (fun _ => ()), ReadsOne I l Z u a 0 (Nat.zero_le _) (fun _ => ()) K0 ∧ (∀ β, (K0 β).lev.Lb = F.to0.cls0.lev.Lb ∧ (K0 β).lev.Uloc = F.to0.cls0.lev.Uloc ∧ (K0 β).lev.U = F.to0.cls0.lev.U ∧ ∀ (κ : (K0 β).lev.U) (κ' : F.to0.cls0.lev.U), κ.1 = κ'.1 → (K0 β).lev.chi κ = F.to0.cls0.lev.chi κ') ∧ ∀ c, ∃ κ : F.to0.cls0.lev.U, ((K0 ((fun _ : (I.stp u a 0).Cl => ()) (I.eCls0 l u a c))).y ⟨I.eCls0 l u a c, rfl⟩).1 = (F.to0.cls0.y c).1 * κ.1 ∧ F.to0.cls0.lev.chi κ = 1 ∧ ∀ v, v ∉ Q → bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1 := by
  first | exact @GlobalTheory.TwU.AtTrue.StepZeroRead.reads | exact GlobalTheory.TwU.AtTrue.StepZeroRead.reads | (intros; apply GlobalTheory.TwU.AtTrue.StepZeroRead.reads <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ComparedFormLevelZeroRealisesComplexPoly
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

set_option maxHeartbeats 1000000 in

theorem cmp_realAt_zero : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → S.Pos → ∀ ι : ℂ →+* ℂ_[D.what₂.places.resChar w], (∀ z : TaylorLogMetric.Qbar, ι z = S.lam z) → letI := wittFractionAlgebraCp (D.what₂.places.resChar w); letI := algKfC S.E.toCEmb; ∀ (d : Dec J std) (h : ((sysS H X std).Pj 0).m + 1 = D.R.N 0) (La : (sysS H X std).Lt 0), ((sysS H X std).Pj 0).IsLatTup La.2 → ∀ x : ((ex.tw.fm u μ).lat 0).V, ∃ V : XR ((sysS H X std).Pj 0) ℂ, MvPolynomial.map (algebraMap (sysS H X std).G.Kf ℂ_[D.what₂.places.resChar w]) ((kaAt X H hT).cmp 0 x La.1 La.2) = MvPolynomial.map ι V ∧ RealAt d 0 (Nat.zero_le _) h La ((ex.tw.fm u μ).emb 0 x) V) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hP ι hι d h La hLa x
  have hpos := (posTie_at S hP ι hι).2
  obtain ⟨g, hg1, hg2⟩ := latticeTupleLevelZero_point_isComponentPoint S hD La hLa
  have hx : x = ex.tw.e0 u μ ((ex.tw.e0 u μ).symm x) := by simp
  generalize (ex.tw.e0 u μ).symm x = x0 at hx
  subst hx
  have K := lev0AtOf_compatible J.Gd.cmp u w hg
  refine ⟨MvPolynomial.map D.what₂.embLL (K.val x0 La.1 La.2), ?_, ?_⟩
  · rw [(kaAt X H hT).cmp_zero, K.val_cmp x0 La.1 La.2 hLa]
    refine (MvPolynomial.map_map _ _ _).trans ((congrArg (MvPolynomial.map · _) ?_).trans (MvPolynomial.map_map _ _ _).symm)
    ext r
    exact (hpos r).symm
  · intro z z' hz
    have hj : (0:ℕ) ≤ D.R.m := Nat.zero_le _
    set c := J.e0.symm (clsAt X H 0 La.1 La.2) with hc
    have hce : clsAt X H 0 La.1 La.2 = J.e0 c := by simp [c]
    have hU := (J.lev0 (J.chart std 0 hj La)).2.2.1
    have hkmem : ((d.kap 0 hj La) : GL (Fin (D.R.N 0)) _) ∈ (J.Gd.forms u).cls0.lev.U := hU ▸ (d.kap 0 hj La).2
    let κ' : (J.Gd.forms u).cls0.lev.U := ⟨(d.kap 0 hj La).1, hkmem⟩
    have hchi := (J.lev0 (J.chart std 0 hj La)).2.2.2 (d.kap 0 hj La) κ' rfl
    obtain ⟨κ0, hy0, hc0, -⟩ := J.y0 c
    have hpt := d.eq 0 hj La hLa
    rw [hce, hy0] at hpt
    have hIs : (lev0At J.Gd u w hg).A.IsPt La.1 g (GlobalTheory.TwU.ratA D.host.F (d.gam 0 hj La) * ((J.Gd.forms u).cls0.y c).1 * (κ0 * κ').1) := by
      convert hg2 using 2
      rw [hpt, Subgroup.coe_mul]
      simp only [mul_assoc]
      rfl
    have hv := K.val_emb x0 La.1 La.2 g hg1 c (d.gam 0 hj La) (d.mem 0 hj La) (κ0 * κ') hIs z z' hz
    have e1 : (((J.Gd.forms u).cls0.lev.chi (κ0 * κ') : ℂˣ) : ℂ) = (((J.Gd.forms u).cls0.lev.chi κ' : ℂˣ) : ℂ) := by
      have e2 := MonoidHom.map_mul (J.Gd.forms u).cls0.lev.chi κ0 κ'
      rw [hc0, one_mul] at e2
      exact congrArg Units.val e2
    rw [e1] at hv
    show _ = _
    rw [cTw_zero]
    simp only [zpow_zero, neg_zero, dPow, detF, Finset.prod_const_one, mul_one]
    refine hv.trans ?_
    have hy : (J.St 0 hj).eY.symm z' = J.jointCmpEmbeddingY ((J.Gd.forms u).val0.eY.symm z') := by
      rw [Equiv.symm_apply_eq, J.fr0, Equiv.apply_symm_apply]
    rw [ex.tw.embed_mul_block_embedding, hce, hy, J.e0Tw, Dec.chi, hchi]

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOffPrimeKernelLatticesOfAgreeAway
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000

namespace GlobalTheory.TwV.Xc

theorem eqOffPrime_of_heq_lattices_rank_eq {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {n m : ℕ} (h : n = m)
    {A B : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} {A' B' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)}
    (ha : HEq A A') (hb : HEq B B') (h' : GL3Theta.EqOff D P A' B') : GL3Theta.EqOff D P A B := by
  subst h
  cases ha
  cases hb
  exact h'

theorem eqOff_kerN_of_sameAway : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ v (P : HeightOneSpectrum (𝓞 D.host.E)), PrimeOf (D.what₂.places.resChar w) ((sysS H X std).G.P.W v) (J.rho std v) P → ∀ j (hj : j ≤ D.R.m) (La Lb : (sysS H X std).Lt j), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → GL3Theta.EqOff D P ((J.fd std).kerN j La) ((J.fd std).kerN j Lb)) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hSpl v P hP j hj La Lb hSA
  have hLa := hSA.1
  have hLb := hSA.2.1
  have h1 := hSA.2.2.1
  have hch : J.chart std j hj La = J.chart std j hj Lb := by
    obtain ⟨c, A⟩ := La
    obtain ⟨c', B⟩ := Lb
    simp only at h1
    subst h1
    exact GlobalTheory.T.latticeTuple_chart_eq_of_same_component S hD hSpl j hj c A B hLa hLb
  have hoff := (GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway S hD hSpl v j hj La Lb hSA).1
  obtain ⟨⟨hr, -⟩, -, hKa, -⟩ := hD j hj La hLa
  obtain ⟨-, -, hKb, -⟩ := hD j hj Lb hLb
  rw [← hch] at hKb
  have key := GlobalTheory.T.kernelLattice_eq_away_from_prime_of_agree_off_place D (D.R.N 0) (D.what₂.places.resChar w) (D.gat u w hg) (A0 J) J.one.int hSpl.1 v P hP (D.R.N j)
    (gramN D j hj) J.a ((J.St j hj).K (J.chart std j hj La)).lev.Lb ((J.St j hj).K (J.chart std j hj La)).lev.Lb_fin
    ((J.St j hj).K (J.chart std j hj La)).lev.Lb_span (J.pt std j hj La).1 (J.pt std j hj Lb).1 hoff
  exact eqOffPrime_of_heq_lattices_rank_eq hr hKa hKb key

end GlobalTheory.TwV.Xc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComparisonSiteDataOverChainCharts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SiteEx

set_option maxHeartbeats 4000000 in

theorem siteD_exists : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (μ : D.what₂.Tup) (J : JIn t u μ), (D.what₂.places.resChar w) ∉ Dx.Qp μ → ∃ Z : SiteD J.Gd.herm u w hg (ex.tw.fm u μ), Z.Fo = foOf J.Hh J.St J.val ∧ SiteGood Z ∧ SiteRest Z ex.cmp ∧ ∀ i hi, Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E (Z.S i hi).B = (J.A.crd (i + 1) hi)⁻¹ := by
  intro D L hT Gi Gl Kc Dx cX ex t u w hg μ J hQ
  have hfr := GlobalTheory.Ggeo.FracLocal.isFractionRing_gat Gl u w hg
  have hrat := GlobalTheory.TwUChiRat.chiRatAll_of_adTie t u μ J.St J.A J.Hh.dt J.a J.tie J.kin
  have hpT : ∀ i (hi : i ≤ D.R.m), ¬ D.what₂.places.resChar w ∣ (J.St i hi).T := fun i hi => by
    rw [J.tie.T_eq i hi]; exact hg.2.2.2.2.2
  have hψ : ∀ i hi, PsiEx (foOf J.Hh J.St J.val i hi) (ex.cmp.embW u w hg) := fun i hi =>
    psiEx_of (foOf J.Hh J.St J.val i hi) (ex.cmp.embW u w hg) hfr (fun β => hrat (i + 1) hi β)
      (fun β => J.ord (i + 1) hi β)
  let Z : SiteD J.Gd.herm u w hg (ex.tw.fm u μ) :=
    { Fo := foOf J.Hh J.St J.val
      chFin := fun i hi => J.fin (i + 1) hi
      S := fun i hi =>
        { B := (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹
          B_lat := fun β => GlobalTheory.T.inv_coords_isBasisAt_baseLattice_of_std_companion J.Gd.herm u w hg hi ((J.St (i + 1) hi).K β).lev (J.A.crd (i + 1) hi) J.a
            (hpT (i + 1) hi) (J.base (i + 1) hi β)
          ψ := fun β => (hψ i hi β).choose
          fin := fun β => fin_of _ β _ } }
  refine ⟨Z, rfl, ⟨fun i hi => hpT (i + 1) hi, fun i hi w' hw' => ?_, fun i hi => trivial⟩, ⟨fun i hi => ?_, fun i hi β => ?_, fun i hi β cl => ?_⟩,
    fun i hi => ?_⟩
  · exact GlobalTheory.TwU.not_mem_underSB_of_gIdx t u w hg μ hQ w' (J.tie.bad (i + 1) hi w' hw')
  · show cT (sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E
        ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹)).1 * gramN D (i + 1) hi *
      (Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E
        ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹)).1 = 1
    rw [MulEquiv.apply_symm_apply]
    exact std_of_C _ _ _ (J.pins.crd_orth (i + 1) hi)
  · exact (hψ i hi β).choose_spec
  · exact chRat_ofChiD J.chiD _ _ _
  · show Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E
        ((Formalism.L2.Forms.reGL (rankN D (i + 1) hi) D.host.E).symm (J.A.crd (i + 1) hi)⁻¹) = _
    exact MulEquiv.apply_symm_apply _ _

end GlobalTheory.SiteEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDatumLevelEquivarianceAtMatrixStepsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_levelEquivariance_at_matrixSteps : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i < t.m2 → PtAway A a i hi → LevAt A dtU a i hi) := by
  first | exact @GlobalTheory.TwV.levAt_mat | exact GlobalTheory.TwV.levAt_mat | (intros; apply GlobalTheory.TwV.levAt_mat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepAdelicDatumLawTargetLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV

noncomputable section

namespace GlobalTheory.CplTarget

section Local

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem xiCpl1_moved (hX : X.Ok) (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) {u : Pr.Word} {al : L.β m2} {b : L.β (m2 + 1)}
    (p : ChPt (R := R) sel mu u m2) (p' q' : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1))))
    (κ : GLQ X.E (R.N (m2 + 1)) (rowSG Pr sel mu)) (c : rowSG Pr sel mu → X.Kˣ)
    (hfr : ∀ P, frsF sel mu q' P = frsF sel mu p' P * ((κ P)⁻¹).1)
    (hc : ∀ P, GlobalTheory.TopLaw.LevAt (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) P (κ P) (c P)) (x : HomE X.E (R.N m2) (R.N (m2 + 1)))
    (hphi : phiT X.K p.deco.1 q'.deco.1 x = phiT X.K p.deco.1 p'.deco.1 x) :
    XiCpl1 Ch sel mu cst L m2 al p q' Y x * ∏ P : rowSG Pr sel mu, rhoS Ch sel mu m2 P ((LinearEquiv.det (κ P).1 : X.Eˣ) : X.E) =
      ((∏ P, c P : X.Kˣ) : X.K) * XiCpl1 Ch sel mu cst L m2 al p p' Y x := by
  unfold XiCpl1
  rw [hphi, mul_assoc, mul_left_comm _ (phiT _ _ _ _), ← Finset.prod_mul_distrib, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun P _ => ?_)
  have e1 : inFr (frsF sel mu p P) (frsF sel mu q' P) x = (κ P).1.toLinearMap ∘ₗ inFr (frsF sel mu p P) (frsF sel mu p' P) x := by
    rw [hfr]
    refine LinearMap.ext fun w => ?_
    rfl
  have e2 : (frsF sel mu q' P).symm (repY Y) = (κ P).1 ((frsF sel mu p' P).symm (repY Y)) := by
    rw [hfr]
    rfl
  rw [e1, e2]
  exact GlobalTheory.CoupledLaw.psiAt_target hX hPr hL (hc P) (L.h m2 al P) _ _

end Local

set_option maxHeartbeats 1000000 in

theorem levAt_target : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i = t.m2 → PtAway A a i hi →
  ∀ β β' (x : UA D i (Nat.le_of_succ_le hi)) (x' x₁' : UA D (i + 1) hi) (κ' : ((St (i + 1) hi).K β').lev.U) p p' p₁',
    x₁'.1 = x'.1 * κ'.1 → IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
    IsPtAd A a (i + 1) hi β' x₁' p₁' → ∀ w,
    muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ'.1) * t.seam.σ₀ (xiPt A i hi β β' p p₁' w) =
      ((((St (i + 1) hi).K β').lev.chi κ' : ℂˣ) : ℂ) * t.seam.σ₀ (xiPt A i hi β β' p p' w)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hT' _hE hMu i hi hi2 hAw β β' x x' x₁' κ' p p' p₁' hx hp hp' hp₁' w
  subst hi2
  obtain ⟨q', κ'', hq', hphi, hfr, hin⟩ := GlobalTheory.T.chartPoint_right_translate_by_level_coupled_step A dtU a hP hT' hi β' x' x₁' κ' p' hx hp'
  obtain ⟨c, hc, hχ⟩ := GlobalTheory.T.coupledStep_chart_level_at_bad_primes A dtU a hP hT' β' κ' κ'' hin
  have hst := GlobalTheory.T.coupledStepChartLevel_keeps_baseCoset A dtU a hP hT' β' κ' κ'' hin
  have hmu := GlobalTheory.T.stepCharacter_det_coupled_eq_prod_local A dtU a hP hT' hMu β' κ' κ'' hin
  have hAw' := hAw β β' x x₁' x x₁' p q' p p₁' hp hq' hp hp₁' fun v _ => ⟨rfl, rfl⟩
  rw [hAw']
  have law := xiCpl1_moved (Ch := t.Ch) (cst := t.cst μ) hP.fields.ok t.pr_ok (t.idx_ok μ) (al := A.ib t.m2 hi β)
    (b := A.ib (t.m2 + 1) (cpl_lt t μ) β') p p' q' (cosetOf A (t.m2 + 1) hi β' p') κ'' c hfr hc w (hphi p w)
  have hcos : cosetOf A (t.m2 + 1) hi β' q' = cosetOf A (t.m2 + 1) hi β' p' := by
    ext y
    unfold cosetOf y0At
    simp only [Set.mem_setOf_eq, dif_pos rfl]
    refine forall_congr' fun P => ?_
    rw [hfr P]
    exact hst P _
  have ex1 : xiPt A t.m2 hi β β' p q' w = XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hi β) p q'
      (cosetOf A (t.m2 + 1) hi β' q') w := by
    unfold xiPt
    rw [dif_neg (lt_irrefl _), if_pos rfl]
  have ex2 : xiPt A t.m2 hi β β' p p' w = XiCpl1 t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 (A.ib t.m2 hi β) p p'
      (cosetOf A (t.m2 + 1) hi β' p') w := by
    unfold xiPt
    rw [dif_neg (lt_irrefl _), if_pos rfl]
  rw [ex1, ex2, hcos, hmu, ← hχ, ← map_mul, ← map_mul, mul_comm (∏ P : SB t μ, _), law]

end GlobalTheory.CplTarget
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepCharacterAtLevelDetMulTameValuesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstCoupledStepCharacter_at_levelDet_mul_tameValues : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU →
  ∀ (hi : t.m2 < D.R.m) (β : (St t.m2 hi.le).Ch) (κ : ((St t.m2 hi.le).K β).lev.U)
    (g : SB t μ → (Sp t.X.E (D.R.N t.m2) ≃ₗ[t.X.E] Sp t.X.E (D.R.N t.m2))) (z : SB t μ → t.X.K),
    (∀ P, A.midRel t.m2 hi β P (g P) (z P) ∧ InFrame t.seam (A.fb t.m2 hi.le β) (t.cst μ).D P κ.1 (g P)) →
    muOf t u μ dtU (t.m2 + 1) (Matrix.GeneralLinearGroup.det κ.1) *
      t.seam.σ₀ (∏ P : SB t μ, rhoS t.Ch t.sel (t.tup μ) t.m2 P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E)) = 1) := by
  first | exact @GlobalTheory.SrcMuDet.muOf_levelDet_mul_sigma_prod_rhoS_eq_one | exact GlobalTheory.SrcMuDet.muOf_levelDet_mul_sigma_prod_rhoS_eq_one | (intros; apply GlobalTheory.SrcMuDet.muOf_levelDet_mul_sigma_prod_rhoS_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeFirstFactorLatticeTuplePoint
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TwV.KerSp

theorem locSp_latK_isPt : ∀ {D : D7} {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) {p : ℕ} {G : GAtP p} (A : LocAt D.host.F D.host.E (D.R.N i) G) (a : 𝓞 D.host.E), (∃ co, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) co) → SplAlg A → LocInt A → LbAtB A lev.Lb → 0 < T → ∀ (c : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)), A.IsPt c g x.1 → ∀ v, IsUnit (T : G.P.W v) → locSp (G.P.W v) (A.iw v) (latK D.sp (gramN D i hi) a x.1 lev.Lb) = colSpan (G.P.W v) ((LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi)).toLinearMap * A.B.1).map (A.iw v) * (castGL A.rk (G.P.Qq v) (g v) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) (G.P.Qq v))) := by
  intro D i hi T bad lev p G A a hco hS hI hB hT c g x hx v hTv
  have hLb : Formalism.L2.GlobalTheoryTheory.Comp.IsLat lev.Lb := ⟨lev.Lb_fin, lev.Lb_span⟩
  have hdual := GlobalTheory.smul_dualSet_latAd_mem D.sp (gramN D i hi) hco T lev.Lb hT hLb lev.Lb_dual x.1 x.2
  have hLA : LatAdLoc A lev.Lb := GlobalTheory.TwV.latAdLoc_of A lev.Lb hS hI lev.Lb_fin lev.Lb_span
  unfold Formalism.MainNotions.G.KAat.latK Formalism.L2.PairingIndexBounds.F.toStd
  rw [GlobalTheory.TwV.locSp_map, GlobalTheory.TwV.CompSp.locSp_compan_eq D.sp (G.P.W v) (G.P.Qq v) (A.iw v) (gramN D i hi) a T _ hTv hdual,
    GlobalTheory.TwV.SpanPt.locSp_latAd_isPt A lev.Lb hLA hB c g x.1 hx v, GlobalTheory.TwV.SpanPt.colSpan_map]
  rw [Matrix.map_mul, Matrix.mul_assoc]
  rfl

end GlobalTheory.TwV.KerSp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelSiteChartBasisOrthonormalLevelIndependentStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelSite_chartBasis_orthonormal_levelIndependent : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (a : Lv.comp j), cT (sigD D : D.host.E →+* D.host.E) (bAt J j hj a).1 * gramN D j hj * (bAt J j hj a).1 = 1 ∧ ∀ a', bAt J j hj a' = bAt J j hj a) := by
  first | exact @GlobalTheory.TwV.DelA.bAt_orth_lev | exact GlobalTheory.TwV.DelA.bAt_orth_lev | (intros; apply GlobalTheory.TwV.DelA.bAt_orth_lev <;> assumption)
end

