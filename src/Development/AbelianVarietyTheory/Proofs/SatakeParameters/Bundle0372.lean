import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RealAt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0365
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0369
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0328
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0032
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0269
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0370
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0358
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0353
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0354
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0352
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0343
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0344
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0342
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0268
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0346
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0039
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0357
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0363
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0359
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChangedFrameRationalUnitary
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries GlobalTheory.TwV GlobalTheory.TwV.DelB GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

theorem sigD_eq_star' (D : D7) (x : D.host.E) : (sigD D : D.host.E →+* D.host.E) x = star x := rfl

theorem cpB_eq_bAt {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I}
  [Fact (D.what₂.places.resChar w).Prime] {t : KerEntTied ex} (J : Joint t H X) (std : Lt.StdAtW D Gl u w hg)
  (j : ℕ) (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j) :
    ((J.cp std).B j La).1.submatrix (Fin.cast ((J.cp std).hk j La)) (Fin.cast ((J.cp std).hk j La)) =
      (bAt J j hj La.1).1.submatrix (Fin.cast h) (Fin.cast h) := by
  cases j with
  | zero => rfl
  | succ i =>
    show (chAt _ _ _ _ _ _ _ _ _ I _ _ _ _ (i + 1) La).B.1.submatrix _ _ = _
    simp only [chAt, dif_pos hj]
    rfl

theorem unitary_product_of_hermitian_relations {E : Type} [Field E] [StarRing E] (σ : E →+* E) (hσ : ∀ x, σ x = star x) {N : ℕ}
    (J c g B : Matrix (Fin N) (Fin N) E) (hc : cT σ c * c = J) (hg : cT σ g * J * g = J) (hB : cT σ B * J * B = 1) :
    star (c * g * B) * (c * g * B) = 1 := by
  have hs : star (c * g * B) = cT σ (c * g * B) := by
    ext i k
    simp only [cT, Matrix.star_apply, Matrix.transpose_apply, Matrix.map_apply, hσ]
  rw [hs, cT_mul, cT_mul]
  calc cT σ B * (cT σ g * cT σ c) * (c * g * B) = cT σ B * (cT σ g * (cT σ c * c) * g) * B := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hc, hg, hB]

theorem changed_frame_unitary : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (d : Dec J std) j (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j), StdU D (mM d j hj La) ∧ FrIs d.fd2 (J.rho std) j La h (mM d j hj La) ∧ (mM d j hj La).1.det * (d.gam j hj La).1.det = (uB J j hj La.1).1.det) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S d j hj h La
  have hB := (GlobalTheory.T.kernelSite_chartBasis_orthonormal_levelIndependent S j hj La.1).1
  have hc := J.pins.crd_orth j hj
  have hg' : (d.gam j hj La)⁻¹ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D j hj) := inv_mem (d.mem j hj La)
  have hval : (mM d j hj La).1 = (J.A.crd j hj).1 * ((d.gam j hj La)⁻¹).1 * (bAt J j hj La.1).1 := by
    simp only [mM, Units.val_mul]
  refine ⟨?_, ?_, ?_⟩
  · unfold StdU
    rw [hval]
    exact unitary_product_of_hermitian_relations _ (sigD_eq_star' D) _ _ _ _ hc hg' hB
  · intro v
    rw [GlobalTheory.T.frM_eq_map_crd_mul_gam_inv_mul_basis S d j hj h La v, cpB_eq_bAt J std j hj h La,
      show ((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E).submatrix (Fin.cast h) (Fin.cast h) =
        ((J.A.crd j hj * (d.gam j hj La)⁻¹ : GL (Fin (D.R.N j)) D.host.E) : Matrix _ _ D.host.E).submatrix (Fin.cast h) (finCongr h) from rfl,
      show (bAt J j hj La.1).1.submatrix (Fin.cast h) (Fin.cast h) = (bAt J j hj La.1).1.submatrix (finCongr h) (Fin.cast h) from rfl,
      Matrix.submatrix_mul_equiv, ← Units.val_mul]
    rfl
  · have hdet : ((d.gam j hj La)⁻¹).1.det * (d.gam j hj La).1.det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    rw [hval, uB, Units.val_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
    linear_combination ((J.A.crd j hj).1.det * (bAt J j hj La.1).1.det) * hdet

end GlobalTheory.TwV.DelA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointsExistAndClassPointsRepresentatives
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.MainNotions.G

noncomputable section

namespace GlobalTheory.TwV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cls

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E}

theorem isPtAd_cls (H : AdTie A dtU a) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.chTw u μ).cls i) :
    IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c) where
  lat := by
    rw [← H.N_eq i hi c]
    exact H.lat i hi c
  frame := fun P => H.frame i hi c P
  fnl := by
    intro P v h hv
    exact Classical.epsilon_spec (H.fnl i hi ((St i hi).chOf c) P v h hv) c rfl

theorem exists_cls_eq (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x : UA D i hi) :
    ∃ c : (D.chTw u μ).cls i, (St i hi).chOf c = β ∧ ∃ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi),
      ∃ κ : ((St i hi).K β).lev.U, x.1 = ratA D.host.F γ * ((St i hi).y c).1 * κ.1 := by
  obtain ⟨⟨c, rfl⟩, hc⟩ := ((St i hi).K β).y_bij.2 (Quotient.mk'' x)
  obtain ⟨g, hg, k, hk, e⟩ := (DoubleCoset.eq _ _ _ _).1 hc
  rw [Subgroup.mem_subgroupOf] at hg hk
  obtain ⟨γ, hγ, hγg⟩ := Subgroup.mem_map.1 hg
  refine ⟨c, rfl, γ, hγ, ⟨k.1, hk⟩, ?_⟩
  have e1 := congrArg Subtype.val e
  simp only [Subgroup.coe_mul] at e1
  rw [e1, ← hγg]
  rfl

end Cls

theorem ptEx_of_tie (hR : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p, ∀ γ ∈ Formalism.UG.UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (Formalism.L2.Forms.gramN D i hi), x'.1 = ratA D.host.F γ * x.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p')) (hL : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x' : UA D i hi) p (κ : ((St i hi).K β).lev.U), x'.1 = x.1 * κ.1 → IsPtAd A a i hi β x p → ∃ p', IsPtAd A a i hi β x' p')) : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a ∧ ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie
  have hcls : ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c) :=
    fun i hi c => isPtAd_cls hTie i hi c
  refine ⟨fun i hi β x => ?_, hcls⟩
  obtain ⟨c, hcβ, γ, hγ, κ, hx⟩ := exists_cls_eq (St := St) i hi β x
  subst hcβ

  let k : UA D i hi := ⟨κ.1, (((St i hi).K ((St i hi).chOf c)).lev.U_eq κ.1).1 κ.2 |>.1⟩

  let x₁ : UA D i hi := x * k⁻¹
  have hx₁ : x₁.1 = ratA D.host.F γ * ((St i hi).y c).1 := by
    show x.1 * (κ.1)⁻¹ = _
    rw [hx, mul_inv_cancel_right]
  obtain ⟨p₁, hp₁⟩ := hR A dtU a hPin hTie i hi _ ((St i hi).y c) x₁ (A.pt i hi c) γ hγ hx₁ (hcls i hi c)
  have hxk : x.1 = x₁.1 * κ.1 := by
    show x.1 = x.1 * (κ.1)⁻¹ * κ.1
    rw [inv_mul_cancel_right]
  exact hL A dtU a hPin hTie i hi _ x₁ x p₁ κ hxk hp₁

theorem ptEx_isPtAd : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a ∧ ∀ i hi c, IsPtAd A a i hi ((St i hi).chOf c) ((St i hi).y c) (A.pt i hi c)) :=
  ptEx_of_tie GlobalTheory.T.chartPoint_leftTranslate_rationalUnitary GlobalTheory.T.chartBasePoint_rightTranslate_by_chartLevel

end GlobalTheory.TwV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DetLatticeTuplesAgreeingAwayFromPlace
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000

theorem GlobalTheory.TwV.Xc.dt_sameAway_step : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ v π, IsUnifAt J v π → ∀ j (hj : j ≤ D.R.m) (La Lb : (sysS H X std).Lt j), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → ∃ k ∈ U1 (sigD D), k ∈ intU D.host.F D.host.E ∧ OneOff ((A0 J).pl v).1 k ∧ (J.fd std).dt j La = (J.fd std).dt j Lb * π ^ (len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2) * k) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS v π hπ j hj La Lb hab
  have hA := hD j hj La hab.1
  have hB := hD j hj Lb hab.2.1
  have pa := GlobalTheory.T.lattice_det_mem_U1_and_ordA_eq_neg_len S hD hS j hj La hab.1
  have pb := GlobalTheory.T.lattice_det_mem_U1_and_ordA_eq_neg_len S hD hS j hj Lb hab.2.1
  have sa := GlobalTheory.T.adelicPoints_agreeAway_of_latticeTuples_agreeAway S hD hS v j hj La Lb hab
  have hone := J.one
  obtain ⟨hadd, hint, -, -⟩ := GlobalTheory.TwV.Xc.OrdA.ordA_props _ _ _ _ _ (A0 J) hone.int hS.1 v
  set n : ℤ := len (sysS H X std) v j Lb.2 - len (sysS H X std) v j La.2 with hn
  set k := ((J.fd std).dt j Lb * π ^ n)⁻¹ * (J.fd std).dt j La with hk

  let oh : (AfE D.host.F D.host.E)ˣ →* Multiplicative ℤ :=
    MonoidHom.mk' (fun x => Multiplicative.ofAdd (ordA (A0 J) v x)) (fun x y => by simp [hadd x y, ofAdd_add])
  have hoh : ∀ x, ordA (A0 J) v x = Multiplicative.toAdd (oh x) := fun x => rfl
  have hkU : k ∈ U1 (sigD D) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ pb.1 (Subgroup.zpow_mem _ hπ.1 n))) pa.1
  have hkOff : OneOff ((A0 J).pl v).1 k := by
    intro w' hw'
    let f : (AfE D.host.F D.host.E)ˣ →* _ := Units.map (prV (E := D.host.E) w').toMonoidHom
    have hfπ : f π = 1 := Units.ext (hπ.2.1 w' hw')
    have hdet : ∀ x : GL (Fin (D.R.N j)) (AfE D.host.F D.host.E),
        f (Matrix.GeneralLinearGroup.det x) = Matrix.GeneralLinearGroup.det (Formalism.UG.bc (prV (E := D.host.E) w') x) := by
      intro x
      apply Units.ext
      simp [f, Formalism.UG.bc, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    have hfab : f ((J.fd std).dt j La) = f ((J.fd std).dt j Lb) := by
      rw [hA.2.2.2, hB.2.2.2, hdet, hdet, sa.1 w' hw']
    have : f k = 1 := by
      simp only [hk, map_mul, map_inv, map_zpow, hfπ, one_zpow, mul_one, hfab, inv_mul_cancel]
    exact congrArg Units.val this
  have hkOrd : ordA (A0 J) v k = 0 := by
    have hz : ordA (A0 J) v (π ^ n) = n * ordA (A0 J) v π := by
      rw [hoh, hoh, map_zpow, toAdd_zpow, smul_eq_mul]
    have hi : ∀ x, ordA (A0 J) v x⁻¹ = -ordA (A0 J) v x := by
      intro x; rw [hoh, hoh, map_inv, toAdd_inv]
    rw [hk, hadd, hi, hadd, hz, pa.2 v, pb.2 v, hπ.2.2, hn]
    ring
  refine ⟨k, hkU, ?_, hkOff, ?_⟩
  · exact GlobalTheory.TwV.Xc.mem_intU_of_oneOff_ordA _ _ (sigD D) _ _ _ (A0 J) _ hone.good hone.int hS.1 v k hkU hkOff hkOrd
  · rw [hk, mul_inv_cancel_left]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FirstCoupledStepAdelicDatumSourceLevelLawStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstCoupledStep_adelicDatum_source_level_law : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i = t.m2 → PtAway A a i hi →
  ∀ β β' (x x₁ : UA D i (Nat.le_of_succ_le hi)) (x' : UA D (i + 1) hi) (κ : ((St i (Nat.le_of_succ_le hi)).K β).lev.U) p p' p₁,
    x₁.1 = x.1 * κ.1 → IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
    IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p₁ → ∀ w,
    ((((St i (Nat.le_of_succ_le hi)).K β).lev.chi κ : ℂˣ) : ℂ) * t.seam.σ₀ (xiPt A i hi β β' p₁ p' w) =
      muOf t u μ dtU (i + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (xiPt A i hi β β' p p' w)) := by
  first | exact @GlobalTheory.LevSrcCpl.levSrc_cpl | exact GlobalTheory.LevSrcCpl.levSrc_cpl | (intros; apply GlobalTheory.LevSrcCpl.levSrc_cpl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrameLocalLatticeSpanKernelLatticeSucc
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

theorem GlobalTheory.TwV.Joint.locSp_kerN_succ : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ j, j + 1 ≤ D.R.m → ∀ La : (sysS H X std).Lt (j + 1), ((sysS H X std).Pj (j + 1)).IsLatTup La.2 → ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN (j + 1) La) = ((sysS H X std).latAt v (j + 1) La.2).map ((((J.fd std).frM (j + 1) La v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J hD j hj La hLa v
  obtain ⟨-, -, hker, -⟩ := hD (j + 1) hj La hLa
  obtain ⟨hTT, hLb, -⟩ := GlobalTheory.T.lattice_tuple_chart_succ_eq_component_chart t std J j hj La hLa
  obtain ⟨-, hpt⟩ := GlobalTheory.T.lattice_tuple_adelic_point_step_succ t std J j hj La
  have hbas := GlobalTheory.T.lattice_tuple_bases_span_at_places t std J (j + 1) La hLa v
  rw [hLb] at hker
  have hcop : Nat.Coprime (I.at' j hj).st.T (D.what₂.places.resChar w) := by
    rw [hTT]
    exact (GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg).2.2.1
  have hp : (D.what₂.places.resChar w).Prime := Fact.out
  have hT0 : 0 < (I.at' j hj).st.T := by
    rcases Nat.eq_zero_or_pos (I.at' j hj).st.T with h0 | h0
    · rw [h0, Nat.coprime_zero_left] at hcop
      exact absurd hcop hp.one_lt.ne'
    · exact h0
  have hun := GlobalTheory.TwV.natCast_isUnit_localRing (sysS H X std) v _ hcop
  have horth : ∃ co, IsOrthCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D (j + 1) hj) co :=
    ⟨_, GlobalTheory.TwV.isOrthCo_toLE_of_cT_mul_self _ _ _ (J.pins.crd_orth (j + 1) hj)⟩
  have hK := GlobalTheory.T.kernelLatticeFirstFactor_latticeTuplePoint ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm La.1).1).lev
    ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1) J.a horth (J.alg j hj _) (H.core j hj _).int (J.lbB j hj _) hT0
    _ _ (J.pt std (j + 1) hj La) hpt v hun
  have hR := @GlobalTheory.TwV.locSp_reindex _ _ _ (D.sp.cm.sig : D.host.E →+* D.host.E) _ _ (_) (_) (_) _ _ _
    ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).rk _ _ _ _ _ hker hK
  have hch := (dif_pos hj : chAt (chainAt H hT) std _ (sysS H X std).unif _ (sysS H X std).eO_spec _ (sysS H X std).dG_spec (sysS H X std).om I
    (lev0At J.Gd u w hg).A (lev0At J.Gd u w hg).J (lev0At J.Gd u w hg).Lb (lev0At J.Gd u w hg).Uloc (j + 1) La = _)
  have hJ := congrArg PtCh.J hch
  have hB := congrArg PtCh.B hch
  have hi := congrArg (fun c => PtCh.iw c v) hch
  have hfr : (J.fd std).frM (j + 1) La v = _ :=
    congrArg (fun M => Matrix.submatrix M (finCongr rfl) (finCongr rfl))
      (congr (congrArg Matrix.map (congr (congrArg HMul.hMul (congrArg (fun Q => LinearMap.toMatrix' (stdCo (D.sp.cm.sig : D.host.E →+* D.host.E) Q).toLinearMap) hJ))
        (congrArg Units.val hB))) (congrArg DFunLike.coe hi))
  rw [hfr, hbas]
  have hiw : J.rho std v = ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm La.1).1).iw v := (J.iw j hj _ v).symm
  rw [hiw]
  exact hR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrameLocalLatticeSpanKernelLatticeZero
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

set_option maxHeartbeats 2000000 in

theorem Joint.locSp_kerN_zero : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std → ∀ La : (sysS H X std).Lt 0, ((sysS H X std).Pj 0).IsLatTup La.2 → ∀ v, locSp ((sysS H X std).G.P.W v) (J.rho std v) ((J.fd std).kerN 0 La) = ((sysS H X std).latAt v 0 La.2).map ((((J.fd std).frM 0 La v).mulVecLin).restrictScalars ((sysS H X std).G.P.W v)) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J hD La hLa v
  obtain ⟨-, -, hK, -⟩ := hD 0 (Nat.zero_le _) La hLa
  rw [(J.lev0 _).1] at hK
  have hcop : Nat.Coprime (D.mem u).A.T (D.what₂.places.resChar w) := (GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg).2.2.1
  have hT0 : 0 < (D.mem u).A.T := by
    rcases Nat.eq_zero_or_pos (D.mem u).A.T with h | h
    · rw [h, Nat.coprime_zero_left] at hcop
      exact absurd hcop (Fact.out : (D.what₂.places.resChar w).Prime).one_lt.ne'
    · exact h
  have hU := GlobalTheory.TwV.natCast_isUnit_localRing (sysS H X std) v _ hcop
  have ho := GlobalTheory.TwV.isOrthCo_toLE_of_cT_mul_self (D.sp.cm.sig : D.host.E →+* D.host.E) _ _ (J.pins.crd_orth 0 (Nat.zero_le _))
  have hs := GlobalTheory.T.kernelLatticeFirstFactor_latticeTuplePoint (J.Gd.forms u).cls0.lev (lev0At J.Gd u w hg).A J.a ⟨_, ho⟩ J.alg0 J.one.int J.lb0 hT0 La.1 _
    (J.pt std 0 (Nat.zero_le _) La) (GlobalTheory.T.lattice_tuple_adelic_point_step_zero t std J La).2 v hU
  rw [GlobalTheory.T.lattice_tuple_bases_span_at_places t std J 0 La hLa v]
  exact locSp_reindex (D.sp.cm.sig : D.host.E →+* D.host.E) _ _ _ (lev0At J.Gd u w hg).A.rk _ _ _ _ _ hK hs

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FramePolynomialsWeightRealisedNextLevelStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_polynomials_weight_realised_next_level : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ) {n : ℕ} (h : (X.Pj (j + 1)).m + 1 = n) (ν : D.what₂.Tau → Fin n → ℕ), (∀ τ r, (ν τ r : ℤ) ≤ cT1 X D pos j τ) → ∀ Q : MvPolynomial (GL3Theta.FrV D n) ℂ, Q ∈ WtPol ℂ ν → ∃ R, Realises X D pos (j + 1) h (wT X D pos j) Q R := by
  first | exact @GlobalTheory.TwV.DelA.realises_of_wtPol | exact GlobalTheory.TwV.DelA.realises_of_wtPol | (intros; apply GlobalTheory.TwV.DelA.realises_of_wtPol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointsAtSplitUnramifiedPlacesOfChainCharts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.Port
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

set_option maxHeartbeats 4000000 in

theorem jointsAt_of_jIn : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (μ : D.what₂.Tup), G.LatTied hT Gi Gl → (∀ u, Nonempty (JIn t u μ)) → GlobalTheory.TwV.JointsAt t μ := by
  intro D L hT Gi Gl Kc Dx cX ex t μ hlt hJ u w hg hw
  obtain ⟨J⟩ := hJ u
  have ht : (Gl.Fl u w hg).t = D.R.t := fl_t ex u w hg
  have hm : (Gl.Fl u w hg).mm = D.R.m := fl_mm_eq ex u w hg
  obtain ⟨Z, hFo, hgood, hrest, -⟩ := GlobalTheory.T.exists_comparisonSiteData_over_chainCharts t u w hg μ J hw
  have H : CmpJHyp ex.cmp (Z.inTw (Gl.Fl u w hg) ht hT) :=
    GlobalTheory.T.comparison_data_statements_at_site J.Gd.herm u w hg ex.tw μ Z (Gl.Fl u w hg) ht hT (fun u => J.Gd.forms u) ex.cmp J.Gd.cmp (fillRec ex u w hg) hgood hrest
  have one := GlobalTheory.T.step_zero_level_statements_of_joint hT ex.cmp J.Gd u w hg J.joint0
  obtain ⟨X, hX⟩ := GlobalTheory.T.exists_labIn_c0_cls_eq_levelZeroClass hT ex.cmp J.Gd u w hg ex.tw μ Z (Gl.Fl u w hg) ht hm hgood J.rat
    (GlobalTheory.chTw_DGam_dvd_mem_DGam t u μ) one J.e0
  obtain ⟨hst, htw⟩ := GlobalTheory.T.comparisonSite_charts_twists_eq_tupleChain J.Gd.herm u w hg ex.tw μ Z (Gl.Fl u w hg) ht hT J.Hh J.St J.val hFo
  obtain ⟨hiw, hpl, hB, hpos, halg, halg0⟩ := GlobalTheory.T.site_localIdentifications_eq_stepZero hT ex.cmp J.Gd u w hg ex.tw μ Z (Gl.Fl u w hg) ht
  refine ⟨Z.lv (Gl.Fl u w hg) ht, Z.inTw (Gl.Fl u w hg) ht hT, H, X, ⟨?_⟩⟩
  exact
  { Gd := J.Gd
    St := J.St
    A := J.A
    dtU := J.Hh.dt
    a := J.a
    pins := J.pins
    tie := J.tie
    st := fun j hj => hst j hj
    e0 := J.e0
    jointCmpEmbeddingY := J.jointCmpEmbeddingY
    e0Tw := J.e0Tw
    one := one
    cls0 := fun c La _ => hX c La
    lev0 := J.lev0
    ch0 := J.ch0
    y0 := J.y0
    fr0 := J.fr0
    iw := hiw
    oneB := hB
    pos := hpos
    tw := htw
    rel := J.rel
    base := J.base
    sharp := GlobalTheory.FormsSharpTie.formsSharpAt_of_pins t u μ J.St J.A J.Hh.dt J.pins (fun _ _ => True) (fun j hj => J.val j hj.le)
    dgen := t.O_dgen u μ ▸ (t.O u μ).dgen_gen
    tied := hlt
    away := hw
    cop := t.cc_rec ▸ GlobalTheory.coprime_absNorm_ccK_of_gIdx D _ _ hg
    empty := Z.lv_empty (Gl.Fl u w hg) ht
    alg := halg
    alg0 := halg0
    lbB := GlobalTheory.T.step_basis_spans_latticeFirstFactor_at_p J.Gd.herm u w hg ex.tw μ Z (Gl.Fl u w hg) ht hT
    lb0 := GlobalTheory.TwV.LbB.lbAtB_lev0At hT ex.cmp J.Gd u w hg J.joint0
    pl := hpl
    kin := J.kin }

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelLatticeDetIdealCharacterEqConstMulDetStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelLattice_detIdeal_character_eq_const_mul_det : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m), ∃ c0 : ℂ, ∀ La : (sysS H X std).Lt j, ((sysS H X std).Pj j).IsLatTup La.2 → IsSDLat D.host.E _ ((J.fd std).kerN j La) → t.χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D _) ((J.fd std).kerN j La)) = c0 * chiI J ((J.fd std).dt j La)) := by
  first | exact @GlobalTheory.TwV.Xc.chi_detId_kerN_eq | exact GlobalTheory.TwV.Xc.chi_detId_kerN_eq | (intros; apply GlobalTheory.TwV.Xc.chi_detId_kerN_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelScalarOfSourceTargetPartsProduct
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelB

theorem tieChiH_of_parts : AllSites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => J.Dict std → ∀ (d : Dec J std) (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]), ∀ j < D.R.m, ∀ (cB : ∀ j, (sysS H X std).Lt j → ℂ_[D.what₂.places.resChar w]) (sc : ∀ j, (sysS H X std).Lv.comp (j + 1) → ((sysS H X std).Pj (j + 1)).Tup → ℂ_[D.what₂.places.resChar w]) (cK : ℂ_[D.what₂.places.resChar w]), (∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → cK * cB j La * ι (d.uS S j La) * ι (d.uT S j La') = sc j La'.1 La'.2) → TieChiH S.Y t u μ (clsAt X H) (fun j => clsAt X H (j + 1)) ι sc (d.sH S ι) cB j cK) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD d ι j hj cB sc cK hsc La hLa c' L' hL'
  have hLat := S.Y.Rep_lat j La hLa
  have hsC := GlobalTheory.T.latticeTuplePairScalar_eq_characterProduct S hD d j hj La (c', L') hLat hL'
  have he := GlobalTheory.T.frameFactors_cancel_p_power_of_pair_series _ (sysS H X std) S.E S.hfin S.hst S.g S.hLT D.what₂.Tau (hT.gat_pos u w hg)
    (FrecG S.E.toCEmb (hT.gat_pos u w hg) (J.fd std) t.B t.χ S.lam (ssRec t u μ) (t.rd u μ).lev (J.xi0 std S.Xi) S.muT (ltC S.g S.hLT)) j La (c', L')
  have h2 := hsc La (c', L') hLat hL'
  show cK * S.E.iK (S.Y.eS j La * (S.Y.eT j (c', L'))⁻¹) * cB j La * (pPow (sysS H X std) j La (c', L') * ι (d.sC S j La (c', L'))) = _
  rw [hsC]
  have hι : ∀ x y : ℂ, ι (x * y) = ι x * ι y := map_mul ι
  simp only [hι]
  linear_combination (cK * cB j La * ι (d.uS S j La) * ι (d.uT S j (c', L')) *
      ι ((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) *
      ι ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) c' L')) : ℂˣ) : ℂ)) * he +
    ι ((GL3Theta.rhoOf D (t.O u μ).mt j ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) *
      ι ((GL3Theta.rhoOf' D (t.O u μ).mt j ((t.O u μ).dt (j + 1) (clsAt X H (j + 1) c' L')) : ℂˣ) : ℂ) * h2

end GlobalTheory.TwV.DelB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepAdelicDatumLevelEquivarianceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStep_adelicDatum_level_equivariance : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i = t.m2 + 1 → PtAway A a i hi → LevAt A dtU a i hi) := by
  first | exact @GlobalTheory.TwTop.levAt_top | exact GlobalTheory.TwTop.levAt_top | (intros; apply GlobalTheory.TwTop.levAt_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleJointDictionaryStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTuple_joint_dictionary : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), J.Dict std := by
  first | exact @GlobalTheory.TwV.joint_dict | exact GlobalTheory.TwV.joint_dict | (intros; apply GlobalTheory.TwV.joint_dict <;> assumption)
end

